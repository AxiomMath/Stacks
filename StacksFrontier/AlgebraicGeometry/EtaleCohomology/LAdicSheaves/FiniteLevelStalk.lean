module

public import Mathlib.CategoryTheory.Sites.JointlySurjective
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Basic
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType

/-!
# Finite-level stalks of an ℓ-adic sheaf

At a geometric point of a Noetherian scheme, an ℓ-adic sheaf has one stalk at each finite
level of coefficients. The transition maps between consecutive levels are surjective, and
each identifies the lower level with the reduction of the higher one modulo `ℓⁿ⁺¹`.

## Main definitions

* `Stacks.EtaleCohomology.finiteLevelStalk` — the module-valued étale stalk at a finite level.
* `Stacks.EtaleCohomology.finiteLevelStalkTransition` — the canonical transition map of stalks.

## Main results

* `Stacks.EtaleCohomology.finite_finiteLevelStalk` — every finite-level stalk is a finite
  module.
* `Stacks.EtaleCohomology.finiteLevelStalkTransition_surjective` — the transition maps are
  surjective.
* `Stacks.EtaleCohomology.finiteLevelStalkTransition_quotient` — the transition identifies the
  quotient of the higher stalk by `ℓⁿ⁺¹` with the lower stalk.

## Implementation notes

Levels are indexed from zero, so level `n` has coefficients in `ℤ/ℓⁿ⁺¹ℤ`. The target of a
transition is regarded, by restriction of scalars, as a module over the coefficient ring of
the source.

## References

* [Stacks Project, Tag 03UQ](https://stacks.math.columbia.edu/tag/03UQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open scoped ChangeOfRings

universe u

namespace Stacks.EtaleCohomology

/-- The colimit of a natural transformation into a right adjoint corresponds, under the
adjunction, to the colimit of its adjunct. -/
lemma colimit_adjunction_homEquiv {I : Type*} [Category I] {C : Type*} [Category C]
    {D : Type*} [Category D] [HasColimitsOfShape I C] [HasColimitsOfShape I D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (F : I ⥤ C) (G : I ⥤ D)
    [PreservesColimit F L] [PreservesColimit G R] (t : F ⟶ G ⋙ R) (f : F ⋙ L ⟶ G)
    (h : ∀ i, adj.homEquiv _ _ (f.app i) = t.app i) :
    colim.map t ≫ (preservesColimitIso R G).inv =
      adj.homEquiv _ _ ((preservesColimitIso L F).hom ≫ colim.map f) := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp] at h ⊢
  apply colimit.hom_ext
  intro i
  simp only [colimit.ι_map_assoc, ι_preservesColimitIso_inv]
  rw [← adj.unit_naturality_assoc]
  simp only [← R.map_comp, ι_preservesColimitIso_hom_assoc, colimit.ι_map]
  rw [R.map_comp, ← Category.assoc, h]

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

/-- The stalk at a geometric point of the level-`n` sheaf of an ℓ-adic sheaf, a module over
`ℤ/ℓⁿ⁺¹ℤ`.

See [Stacks Project, Tag 03UQ](https://stacks.math.columbia.edu/tag/03UQ). -/
public abbrev finiteLevelStalk (F : LAdicSheaf B X ℓ) (s : GeometricPoint X.1) (n : ℕ) :
    ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))) :=
  etaleStalk B X.1 X.property s (F.level n).obj

/-- A geometric point of `X` as a point of the small étale site of `X`: its fibre is the
category of étale neighbourhoods, which is cofiltered, essentially small, and jointly
surjective for the étale topology. -/
private noncomputable def finiteLevelStalkPoint (s : GeometricPoint X.1) :
    (SmallEtale.topology B X.1 X.property).Point where
  fiber := geometricPointFiber B X.1 X.property s
  isCofiltered := isCofiltered_geometricPointFiber_elements B X.1 X.property s
  initiallySmall := inferInstance
  jointly_surjective := by
    intro U R hR x
    change (SmallEtale.precoverage B X.1 X.property).Saturate U R at hR
    induction hR with
    | of U P hP =>
      obtain ⟨E, hEq, hE⟩ := (SmallEtale.mem_precoverage_iff B X.1 X.property).1 hP
      subst P
      let E0 := PreZeroHypercover.map (SmallEtale.inclusion B X.1 X.property) E
      let E1 := PreZeroHypercover.map (Over.forget (B.obj X.1 X.property)) E0
      let E' : PreZeroHypercover.{u + 1} ((SmallEtale.toScheme B X.1 X.property).obj U) :=
        PreZeroHypercover.map (schemeBelowInclusion B.cutoff) E1
      have h11' : E'.presieve₀ ∈ Scheme.jointlySurjectivePrecoverage.coverings
          ((SmallEtale.toScheme B X.1 X.property).obj U) := by
        simpa [E', E1, E0, SmallEtale.toScheme, BigEtaleOver.toScheme] using hE.1.1
      have h12' : E'.presieve₀ ∈ (MorphismProperty.precoverage @Etale).coverings
          ((SmallEtale.toScheme B X.1 X.property).obj U) := by
        simpa [E', E1, E0, SmallEtale.toScheme, BigEtaleOver.toScheme] using hE.1.2
      obtain ⟨i, y, hy⟩ :=
        (Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff Scheme.forget).mp h11'
          (x.1 default)
      let iE : E.I₀ := i
      have hEt : Etale (E'.f i) := (MorphismProperty.ofArrows_mem_precoverage.mp h12') i
      obtain ⟨g, hg, hgy⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (E'.f i) x.1 y hy
      have hY : E'.X i = (SmallEtale.toScheme B X.1 X.property).obj (E.X iE) := rfl
      have hcomm : (SmallEtale.toScheme B X.1 X.property).map (E.f iE) ≫
          B.inclusion.map U.obj.hom = B.inclusion.map (E.X iE).obj.hom :=
        SmallEtale.toScheme_map_comp B X.1 X.property (E.f iE)
      have hfi : E'.f i = (SmallEtale.toScheme B X.1 X.property).map (E.f iE) := by
        dsimp [E', E1, E0, PreZeroHypercover.map, SmallEtale.toScheme, BigEtaleOver.toScheme]
      have heq : eqToHom hY ≫
          (SmallEtale.toScheme B X.1 X.property).map (E.f iE) = E'.f i := by
        rw [show hY = rfl by apply Subsingleton.elim]
        change (SmallEtale.toScheme B X.1 X.property).map (E.f iE) = E'.f i
        exact hfi.symm
      have hcomp : (g ≫ eqToHom hY) ≫
          (SmallEtale.toScheme B X.1 X.property).map (E.f iE) = g ≫ E'.f i := by
        simpa only [Category.assoc] using congrArg (fun q => g ≫ q) heq
      refine ⟨E.X iE, E.f iE, ?_, ⟨g ≫ eqToHom hY, ?_⟩, ?_⟩
      · simpa [PreZeroHypercover.presieve₀] using (Sieve.ofArrows_mk E.X E.f iE)
      · calc
          (g ≫ eqToHom hY) ≫ B.inclusion.map (E.X iE).obj.hom =
              (g ≫ eqToHom hY) ≫ ((SmallEtale.toScheme B X.1 X.property).map (E.f iE) ≫
                B.inclusion.map U.obj.hom) :=
                congrArg (fun q => (g ≫ eqToHom hY) ≫ q) hcomm.symm
          _ = (g ≫ E'.f i) ≫ B.inclusion.map U.obj.hom :=
                congrArg (fun q => q ≫ B.inclusion.map U.obj.hom) hcomp
          _ = x.1 ≫ B.inclusion.map U.obj.hom := by rw [hg]
          _ = s.hom := x.2
      · apply Subtype.ext
        calc
          (g ≫ eqToHom hY) ≫ (SmallEtale.toScheme B X.1 X.property).map (E.f iE) =
              g ≫ E'.f i := hcomp
          _ = x.1 := hg
    | top U => exact ⟨U, 𝟙 U, by simp, x, by simp⟩
    | pullback U S hS V f ih =>
      obtain ⟨W, g, hg, z, hz⟩ := ih ((geometricPointFiber B X.1 X.property s).map f x)
      let Fib := geometricPointFiber B X.1 X.property s
      let dV : Fib.Elements := ⟨V, x⟩
      let dW : Fib.Elements := ⟨W, z⟩
      let dU : Fib.Elements := ⟨U, Fib.map f x⟩
      let fV : dV ⟶ dU := CategoryOfElements.homMk dV dU f rfl
      let fW : dW ⟶ dU := CategoryOfElements.homMk dW dU g hz
      obtain ⟨q, qV, qW, hq⟩ := IsCofiltered.cospan fV fW
      have hmaps : qV.val ≫ f = qW.val ≫ g := congrArg Subtype.val hq
      refine ⟨q.1, qV.val, ?_, q.2, ?_⟩
      · change S (qV.val ≫ f)
        rw [hmaps]
        exact S.downward_closed hg qW.val
      · exact qV.property
    | transitive U S R hS hlocal ihS ihlocal =>
      obtain ⟨V, f, hf, y, hy⟩ := ihS x
      obtain ⟨W, g, hg, z, hz⟩ := ihlocal hf y
      refine ⟨W, g ≫ f, ?_, z, ?_⟩
      · exact hg
      · simp [hz, hy]

/-- The stalk of the scalar reduction of the level-`n+1` sheaf is the scalar extension of the
level-`n+1` stalk. -/
private noncomputable def finiteLevelStalkScalarComparison
    (F : LAdicSheaf B X ℓ) (s : GeometricPoint X.1) (n : ℕ) :
    ((finiteLevelStalkPoint B X s).sheafFiber.{u, u, u + 1, u + 1, u + 2}
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))).obj
      ((F.level (n + 1)).scalarReduction B X ℓ n)) ≅
    (ModuleCat.extendScalars.{0, 0, u + 1} (finiteLevelRingHom ℓ n)).obj
      (finiteLevelStalk B X ℓ F s (n + 1)) := by
  let J := SmallEtale.topology B X.1 X.property
  let Φ : J.Point.{u, u, u + 1} := finiteLevelStalkPoint B X s
  letI := Φ.isCofiltered
  letI := Φ.initiallySmall
  letI : HasWeakSheafify J (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) := inferInstance
  letI : HasColimitsOfSize.{u, u, u + 1, u + 2} (ModuleCat.{u + 1, 0} (ZMod (ℓ ^ (n + 1)))) :=
    ModuleCat.hasColimitsOfSize.{u + 1, 0, u, u} (ZMod (ℓ ^ (n + 1)))
  letI : HasLimitsOfSize.{u, u, u + 1, u + 2} (ModuleCat.{u + 1, 0} (ZMod (ℓ ^ (n + 1)))) :=
    ModuleCat.instHasLimitsOfSize.{u + 1, u, 0}
  let E : ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 2))) ⥤ ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))) :=
    ModuleCat.extendScalars.{0, 0, u + 1} (finiteLevelRingHom ℓ n)
  let C : Type (u + 1) := SmallEtale B X.1 X.property
  let P : Cᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))) := (F.level (n + 1)).obj ⋙ E
  let e₁ := (Φ.presheafToSheafCompSheafFiberIso
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).app P
  let e₂ := (preservesColimitIso E
    (((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op) ⋙
      (F.level (n + 1)).obj)).symm
  exact e₁ ≪≫ e₂

/-- The fibre of the level-`n` sheaf at the site point attached to a geometric point is the
level-`n` stalk. -/
private noncomputable def finiteLevelStalkFiberComparison
    (F : LAdicSheaf B X ℓ) (s : GeometricPoint X.1) (n : ℕ) :
    ((finiteLevelStalkPoint B X s).sheafFiber).obj (F.level n) ≅
      finiteLevelStalk B X ℓ F s n := by
  dsimp [finiteLevelStalk, finiteLevelStalkPoint, GrothendieckTopology.Point.sheafFiber,
    GrothendieckTopology.Point.presheafFiber, etaleStalk]
  exact Iso.refl _

/-- The map on stalks induced by the scalar reduction of a transition of an ℓ-adic sheaf. -/
private noncomputable def finiteLevelStalkScalarReductionMap
    (F : LAdicSheaf B X ℓ) (s : GeometricPoint X.1) (n : ℕ) :
    (ModuleCat.extendScalars.{0, 0, u + 1} (finiteLevelRingHom ℓ n)).obj
        (finiteLevelStalk B X ℓ F s (n + 1)) ⟶
      finiteLevelStalk B X ℓ F s n :=
  (finiteLevelStalkScalarComparison B X ℓ F s n).inv ≫
    ((finiteLevelStalkPoint B X s).sheafFiber.map
      (FiniteLevelSheaf.scalarReductionMap B X ℓ n
        (F.level (n + 1)) (F.level n) (F.transition n))) ≫
    (finiteLevelStalkFiberComparison B X ℓ F s n).hom

/-- The map on stalks induced by the scalar reduction of a transition is an isomorphism. -/
private theorem finiteLevelStalkScalarReductionMap_isIso
    (F : LAdicSheaf B X ℓ) (s : GeometricPoint X.1) (n : ℕ) :
    IsIso (finiteLevelStalkScalarReductionMap B X ℓ F s n) := by
  have := F.reduction_isIso n
  unfold finiteLevelStalkScalarReductionMap
  infer_instance

/-- The transition between consecutive finite-level stalks of an ℓ-adic sheaf, linear over the
coefficient ring of the higher level.

See [Stacks Project, Tag 03UQ](https://stacks.math.columbia.edu/tag/03UQ). -/
public noncomputable def finiteLevelStalkTransition (F : LAdicSheaf B X ℓ)
    (s : GeometricPoint X.1) (n : ℕ) :
    finiteLevelStalk B X ℓ F s (n + 1) ⟶
      (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)).obj
        (finiteLevelStalk B X ℓ F s n) :=
  colim.map (Functor.whiskerLeft
    ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op)
    (F.transition n).hom) ≫
    (preservesColimitIso (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n))
      (((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op) ⋙
        (F.level n).obj)).inv

/-- The transition on stalks is the adjunct of the map induced by scalar reduction. -/
private theorem finiteLevelStalkTransition_eq_scalarReductionMap (F : LAdicSheaf B X ℓ)
    (s : GeometricPoint X.1) (n : ℕ) :
    finiteLevelStalkTransition B X ℓ F s n =
      (ModuleCat.extendRestrictScalarsAdj (finiteLevelRingHom ℓ n)).homEquiv _ _
        (finiteLevelStalkScalarReductionMap B X ℓ F s n) := by
  let J := SmallEtale.topology B X.1 X.property
  let π := (CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op
  let E := ModuleCat.extendScalars.{0, 0, u + 1} (finiteLevelRingHom ℓ n)
  let R := ModuleCat.restrictScalars.{u + 1, 0, 0} (finiteLevelRingHom ℓ n)
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, 0} (finiteLevelRingHom ℓ n)
  let A := π ⋙ (F.level (n + 1)).obj
  let G := π ⋙ (F.level n).obj
  let r := FiniteLevelSheaf.scalarReductionMap B X ℓ n
    (F.level (n + 1)) (F.level n) (F.transition n)
  let a := toSheafify J ((F.level (n + 1)).obj ⋙ E)
  let k := Functor.whiskerLeft π (a ≫ r.hom)
  have hmap : finiteLevelStalkScalarReductionMap B X ℓ F s n =
      (preservesColimitIso E A).hom ≫ colim.map k := by
    show (preservesColimitIso E A).hom ≫ colim.map (Functor.whiskerLeft π a) ≫
      colim.map (Functor.whiskerLeft π r.hom) ≫ 𝟙 _ = _
    simp only [k, Functor.whiskerLeft_comp, Functor.map_comp, Category.comp_id]
  rw [hmap]
  apply colimit_adjunction_homEquiv adj A G
  intro i
  have h := FiniteLevelSheaf.scalarReductionMap_comp B X ℓ n
    (F.level (n + 1)) (F.level n) (F.transition n)
  rw [Adjunction.homEquiv_unit] at h
  have hi := congrArg (fun t => t.hom.app (π.obj i)) h
  simp only [ObjectProperty.FullSubcategory.comp_hom, Sheaf.adjunction_unit_app_hom,
    sheafCompose_map_hom] at hi
  change (adj.unit.app (A.obj i) ≫ R.map (a.app (π.obj i))) ≫ R.map (r.hom.app (π.obj i)) =
    (F.transition n).hom.app (π.obj i) at hi
  simpa only [Adjunction.homEquiv_unit, k, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.map_comp, Category.assoc] using hi

/-- The transition on stalks is the unit of extension–restriction followed by the restriction
of the map induced by scalar reduction. -/
private theorem finiteLevelStalkTransition_eq_unit_comp (F : LAdicSheaf B X ℓ)
    (s : GeometricPoint X.1) (n : ℕ) :
    finiteLevelStalkTransition B X ℓ F s n =
      (ModuleCat.extendRestrictScalarsAdj (finiteLevelRingHom ℓ n)).unit.app
          (finiteLevelStalk B X ℓ F s (n + 1)) ≫
        (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)).map
          (finiteLevelStalkScalarReductionMap B X ℓ F s n) := by
  rw [finiteLevelStalkTransition_eq_scalarReductionMap, Adjunction.homEquiv_unit]

/-- The kernel of the reduction `ℤ/nℤ → ℤ/mℤ` is generated by `m`. -/
private theorem zmod_castHom_ker {m n : ℕ} (h : m ∣ n) :
    RingHom.ker (ZMod.castHom h (ZMod m)) = Ideal.span ({(m : ZMod n)} : Set (ZMod n)) := by
  ext x
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
    obtain ⟨k, hk⟩ :=
      (CharP.intCast_eq_zero_iff (ZMod m) m z).mp (by simpa [RingHom.mem_ker] using hx)
    exact ⟨k, by simp [hk]⟩
  · rintro ⟨y, rfl⟩
    show (ZMod.castHom h (ZMod m)) ((m : ZMod n) * y) = 0
    rw [map_mul, map_natCast]
    simp

/-- Along a surjective ring map the unit of the extension–restriction adjunction is
surjective. -/
private theorem scalarExtensionUnit_surjective {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (M : ModuleCat.{u + 1} R) :
    Function.Surjective
      ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, 0} f).unit.app M).hom := by
  intro z
  let _ : Module R S := Module.compHom S f
  let SR : ModuleCat R := (ModuleCat.restrictScalars f).obj (ModuleCat.of S S)
  let one : ↑SR := (1 : S)
  show ∃ m : (M : Type (u + 1)), one ⊗ₜ[R] m = z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul s m =>
    obtain ⟨r, rfl⟩ := hf s
    refine ⟨r • m, ?_⟩
    show (1 : S) ⊗ₜ[R] (r • m) = f r ⊗ₜ[R] m
    rw [← TensorProduct.smul_tmul, show (r • (1 : S) : S) = f r from mul_one (f r)]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, TensorProduct.tmul_add _ _ _⟩

/-- Along a surjective ring map the kernel of the unit of the extension–restriction adjunction
is the kernel ideal times the module. -/
private theorem scalarExtensionUnit_ker {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (M : ModuleCat.{u + 1} R) :
    LinearMap.ker ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, 0} f).unit.app M).hom =
      RingHom.ker f • (⊤ : Submodule R (M : Type (u + 1))) := by
  let I : Ideal R := RingHom.ker f
  let _ : Algebra R S := RingHom.toAlgebra f
  let qeq : (R ⧸ I) ≃ₐ[R] S :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hf
  let t : TensorProduct R (R ⧸ I) (M : Type (u + 1)) ≃ₗ[R]
      TensorProduct R S (M : Type (u + 1)) :=
    TensorProduct.congr qeq.toLinearEquiv (LinearEquiv.refl R (M : Type (u + 1)))
  let e : TensorProduct R S (M : Type (u + 1)) ≃ₗ[R]
      (M : Type (u + 1)) ⧸ (I • (⊤ : Submodule R (M : Type (u + 1)))) :=
    t.symm ≪≫ₗ TensorProduct.quotTensorEquivQuotSMul (M : Type (u + 1)) I
  let η := (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, 0} f).unit.app M
  have hη (x : M) : η.hom x = (1 : S) ⊗ₜ[R,f] x :=
    ModuleCat.extendRestrictScalarsAdj_unit_app_apply f M x
  have he (x : M) : e ((1 : S) ⊗ₜ[R,f] x) = Submodule.Quotient.mk x := by
    show TensorProduct.quotTensorEquivQuotSMul (M : Type (u + 1)) I
      (qeq.symm 1 ⊗ₜ[R] x) = _
    have hq : qeq.symm (1 : S) = Ideal.Quotient.mk I (1 : R) := by simp [qeq]
    rw [hq]
    exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I x
  ext x
  show η.hom x = 0 ↔ x ∈ I • (⊤ : Submodule R (M : Type (u + 1)))
  constructor
  · intro hx
    have hη0 : (1 : S) ⊗ₜ[R,f] x = 0 := by
      rw [← hη]
      exact hx
    have hh : (Submodule.Quotient.mk x :
        (M : Type (u + 1)) ⧸ (I • (⊤ : Submodule R (M : Type (u + 1))))) = 0 := by
      calc
        Submodule.Quotient.mk x = e (η.hom x) := by rw [hη, he]
        _ = 0 := by rw [hη, hη0]; simp
    exact (Submodule.Quotient.mk_eq_zero _).mp hh
  · intro hx
    have hh : e (η.hom x) = e 0 := by
      rw [hη, he]
      simpa using (Submodule.Quotient.mk_eq_zero _).mpr hx
    exact e.injective hh

/-- Every finite-level stalk of an ℓ-adic sheaf at a geometric point is finite. -/
@[stacks 03UQ "finite_level_stalks"]
public theorem finite_finiteLevelStalk (F : LAdicSheaf B X ℓ) (s : GeometricPoint X.1) (n : ℕ) :
    Finite (finiteLevelStalk B X ℓ F s n) := by
  let K : CochainComplex
      (Sheaf (SmallEtale.topology B X.1 X.property)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))) ℤ :=
    HomologicalComplex.mk (fun _ => F.level n) (fun _ _ => 0) (by intros; rfl) (by intros; simp)
  have hfin : Module.Finite (ZMod (ℓ ^ (n + 1)))
      ((etaleModuleStalkFunctor.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) s).obj (F.level n)) :=
    stalk_finite.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) K (fun _ => F.constructible n) s n
  have htype :
      Finite ((etaleModuleStalkFunctor.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) s).obj
        (F.level n)) :=
    Module.finite_of_finite (ZMod (ℓ ^ (n + 1)))
  simpa [finiteLevelStalk, etaleModuleStalkFunctor, etaleStalkPresheafFunctor, etaleStalk]
    using htype

/-- Each transition between consecutive finite-level stalks is surjective. -/
@[stacks 03UQ "finite_level_stalks"]
public theorem finiteLevelStalkTransition_surjective (F : LAdicSheaf B X ℓ)
    (s : GeometricPoint X.1) (n : ℕ) :
    Function.Surjective (finiteLevelStalkTransition B X ℓ F s n).hom := by
  let f := finiteLevelRingHom ℓ n
  have hf : Function.Surjective f := ZMod.castHom_surjective _
  let M := finiteLevelStalk B X ℓ F s (n + 1)
  let g := finiteLevelStalkScalarReductionMap B X ℓ F s n
  let adj := ModuleCat.extendRestrictScalarsAdj f
  have htransition := finiteLevelStalkTransition_eq_unit_comp B X ℓ F s n
  have hunit := scalarExtensionUnit_surjective f hf M
  let _ : IsIso g := finiteLevelStalkScalarReductionMap_isIso B X ℓ F s n
  intro y
  have hg : Function.Surjective g.hom := fun z ↦ ⟨(inv g).hom z, by simp⟩
  obtain ⟨z, hz⟩ := hg y
  obtain ⟨x, hx⟩ := hunit z
  refine ⟨x, ?_⟩
  rw [htransition]
  show (ModuleCat.Hom.hom g) ((ModuleCat.Hom.hom (adj.unit.app M)) x) = y
  rw [hx, hz]

/-- The transition identifies the quotient of the level-`n+1` stalk by `ℓⁿ⁺¹` with the
level-`n` stalk. -/
@[stacks 03UQ "finite_level_stalks"]
public theorem finiteLevelStalkTransition_quotient (F : LAdicSheaf B X ℓ)
    (s : GeometricPoint X.1) (n : ℕ) :
    ∃ e : (finiteLevelStalk B X ℓ F s (n + 1) ⧸
        (Ideal.span ({(ℓ ^ (n + 1) : ZMod (ℓ ^ (n + 2)))} : Set (ZMod (ℓ ^ (n + 2))))) •
          (⊤ : Submodule (ZMod (ℓ ^ (n + 2))) (finiteLevelStalk B X ℓ F s (n + 1))))
        ≃ₗ[ZMod (ℓ ^ (n + 2))]
          (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)).obj
            (finiteLevelStalk B X ℓ F s n),
      ∀ x, e (Submodule.Quotient.mk x) = (finiteLevelStalkTransition B X ℓ F s n).hom x := by
  let f := finiteLevelRingHom ℓ n
  let M := finiteLevelStalk B X ℓ F s (n + 1)
  let g := finiteLevelStalkScalarReductionMap B X ℓ F s n
  let adj := ModuleCat.extendRestrictScalarsAdj f
  let T : (M : Type (u + 1)) →ₗ[ZMod (ℓ ^ (n + 2))]
      (ModuleCat.restrictScalars f).obj (finiteLevelStalk B X ℓ F s n) :=
    (finiteLevelStalkTransition B X ℓ F s n).hom
  have hf : Function.Surjective f := ZMod.castHom_surjective _
  have hsurj : Function.Surjective T := by
    simpa [T] using finiteLevelStalkTransition_surjective B X ℓ F s n
  have htransition := finiteLevelStalkTransition_eq_unit_comp B X ℓ F s n
  have hkerUnit : LinearMap.ker ((adj.unit.app M).hom) =
      RingHom.ker f • (⊤ : Submodule (ZMod (ℓ ^ (n + 2))) (M : Type (u + 1))) :=
    scalarExtensionUnit_ker f hf M
  have hginj : Function.Injective g.hom := by
    have : IsIso g := finiteLevelStalkScalarReductionMap_isIso B X ℓ F s n
    intro x y h
    simpa using congrArg (inv g).hom h
  have hginjR : Function.Injective ((ModuleCat.restrictScalars f).map g).hom := hginj
  have hker : LinearMap.ker T =
      (Ideal.span ({(ℓ ^ (n + 1) : ZMod (ℓ ^ (n + 2)))} : Set (ZMod (ℓ ^ (n + 2))))) •
        (⊤ : Submodule (ZMod (ℓ ^ (n + 2))) (M : Type (u + 1))) := by
    have hT : T = ((ModuleCat.restrictScalars f).map g).hom.comp (adj.unit.app M).hom := by
      have hh := congrArg (fun φ => φ.hom) htransition
      simpa [T, ModuleCat.hom_comp] using hh
    rw [hT, LinearMap.ker_comp]
    have hgker : LinearMap.ker ((ModuleCat.restrictScalars f).map g).hom = ⊥ :=
      LinearMap.ker_eq_bot.mpr hginjR
    rw [hgker, Submodule.comap_bot, hkerUnit]
    have hdiv : ℓ ^ (n + 1) ∣ ℓ ^ (n + 2) := pow_dvd_pow ℓ (by omega : n + 1 ≤ n + 2)
    have hI : RingHom.ker f =
        Ideal.span ({(ℓ ^ (n + 1) : ZMod (ℓ ^ (n + 2)))} : Set (ZMod (ℓ ^ (n + 2)))) := by
      simpa [f, finiteLevelRingHom] using
        (zmod_castHom_ker (m := ℓ ^ (n + 1)) (n := ℓ ^ (n + 2)) hdiv)
    rw [hI]
  let K : Submodule (ZMod (ℓ ^ (n + 2))) (M : Type (u + 1)) :=
    (Ideal.span ({(ℓ ^ (n + 1) : ZMod (ℓ ^ (n + 2)))} : Set (ZMod (ℓ ^ (n + 2))))) • ⊤
  let eKer := Submodule.quotEquivOfEq K (LinearMap.ker T) hker.symm
  let e₀ := T.quotKerEquivOfSurjective hsurj
  refine ⟨eKer.trans e₀, ?_⟩
  intro x
  simp [eKer, e₀, K, LinearMap.quotKerEquivOfSurjective_apply_mk, T]

end Stacks.EtaleCohomology

end
