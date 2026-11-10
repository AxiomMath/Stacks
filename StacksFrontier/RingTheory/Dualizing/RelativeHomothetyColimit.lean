module

public import StacksFrontier.Homology.RelativelyPerfect.ColimitHom
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsSelfIso
public import StacksFrontier.RingTheory.Dualizing.RelativeHomothetySelfExt
import StacksFrontier.RingTheory.Dualizing.RelativeEndomorphisms

/-!
# Self-extensions over a filtered colimit of rings

Let `R` be the filtered colimit of `R₀`-algebras `Rᵢ`, let `R₀ → A₀` be flat of finite
presentation and let `K₀` in `D(A₀)` be pseudo-coherent of finite Tor dimension over `R₀`.  By the
morphism-set half of [stacks 0DHX] every morphism between derived base changes of `K₀` to
`A = R ⊗[R₀] A₀` comes from a finite stage. Hence if scalars exhaust the endomorphisms of the base
change of `K₀` at every stage, they do over `A`; and if there is no nonzero morphism from the base
change of `K₀` to that of `L₀` at every stage, there is none over `A`. Moreover a ring is the
filtered colimit of its finitely generated subalgebras, derived extension of scalars is linear and
commutes with shifts, and finite Tor dimension is stable under shifts.

## Main results

* `Dualizing.surjective_smul_id_limitDerivedObj`: if scalars exhaust the endomorphisms of the base
  change of `K₀` at every stage, they do over `A`.
* `Dualizing.subsingleton_limitDerivedObj`: if there is no nonzero morphism between the base
  changes of `K₀` and `L₀` at every stage, there is none over `A`.
* `Dualizing.fgSubalgebraCoconeIsColimit`: `R` is the filtered colimit of its finitely generated
  `R₀`-subalgebras.
* `Dualizing.totalDerivedExtensionScalars_map_smul`: derived extension of scalars along `g`
  carries `b • φ` to `g b • φ`.

## References

* [Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
* [Stacks Project, Tag 0E2G](https://stacks.math.columbia.edu/tag/0E2G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard

universe u

noncomputable section

section Linearity

open scoped ModuleCat.Algebra

/-- A left adjoint is linear as soon as its right adjoint is. -/
private alias left_adjoint_linear' := left_adjoint_linear

/-- Restriction of scalars along `g` is `B`-linear. -/
private theorem restrictScalars_linear {B C : Type u} [CommRing B] [CommRing C] (g : B →+* C) :
    let : Algebra B C := g.toAlgebra
    (ModuleCat.restrictScalars.{u} g).Linear B := by
  let : Algebra B C := g.toAlgebra
  exact inferInstanceAs ((ModuleCat.restrictScalars.{u} (Algebra.ofId B C).toRingHom).Linear B)

/-- Derived extension of scalars along `g` carries `b • φ` to `g b • φ`. -/
theorem totalDerivedExtensionScalars_map_smul {B C : Type u} [CommRing B] [CommRing C]
    (g : B →+* C) {X Y : DerivedCategory (ModuleCat.{u} B)} (φ : X ⟶ Y) (b : B) :
    (totalDerivedExtensionScalars.{u, u, u} g).functor.map (b • φ) =
      g b • (totalDerivedExtensionScalars.{u, u, u} g).functor.map φ := by
  let : Algebra B C := g.toAlgebra
  let G := ModuleCat.restrictScalars.{u} g
  have : G.Linear B := restrictScalars_linear g
  let E := totalDerivedExtensionScalars.{u, u, u} g
  let adj : E.functor ⊣ G.mapDerivedCategory :=
    @derivedExtensionScalarsAdjunction.{u, u, u} B C _ _ g _ _ E.functor E.comparison
      E.isLeftDerived
  let : E.functor.Linear B := left_adjoint_linear' adj
  rw [Functor.map_smul]
  rfl

/-- Derived restriction of scalars along `g` carries `g b • φ` to `b • φ`. -/
theorem restrictScalars_mapDerivedCategory_map_smul {B C : Type u} [CommRing B] [CommRing C]
    (g : B →+* C) {X Y : DerivedCategory (ModuleCat.{u} C)} (φ : X ⟶ Y) (b : B) :
    (ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map (g b • φ) =
      b • (ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map φ := by
  let : Algebra B C := g.toAlgebra
  let G := ModuleCat.restrictScalars.{u} g
  have : G.Linear B := restrictScalars_linear g
  change G.mapDerivedCategory.map (b • φ) = b • G.mapDerivedCategory.map φ
  rw [Functor.map_smul]

end Linearity

/-! ### Transport of the two conditions -/

section Transport

variable {R S : Type*} [CommRing R] [CommRing S] {C D : Type*} [Category C] [Category D]
  [Preadditive C] [Preadditive D] [Linear R C] [Linear S D]

/-- If every endomorphism of `Y` is a scalar multiple of the identity, then so is every
endomorphism of an object isomorphic to `Y`. -/
theorem surjective_smul_id_of_iso {X Y : C} (e : X ≅ Y)
    (h : Function.Surjective (fun a : R => a • 𝟙 Y)) :
    Function.Surjective (fun a : R => a • 𝟙 X) := by
  intro f
  obtain ⟨a, ha⟩ := h (e.inv ≫ f ≫ e.hom)
  refine ⟨a, ?_⟩
  have h' : e.hom ≫ (a • 𝟙 Y) ≫ e.inv = e.hom ≫ (e.inv ≫ f ≫ e.hom) ≫ e.inv :=
    congrArg (fun z => e.hom ≫ z ≫ e.inv) ha
  simpa [Linear.comp_smul, Linear.smul_comp] using h'

/-- Every endomorphism being a scalar multiple of the identity is reflected by a faithful functor
which carries the multiple by the image of a scalar to the scalar multiple. -/
theorem surjective_smul_id_of_faithful (Φ : C ⥤ D) [Φ.Faithful] (σ : S → R)
    (hσ : ∀ (s : S) (X : C), Φ.map (σ s • 𝟙 X) = s • 𝟙 (Φ.obj X)) (K : C)
    (h : Function.Surjective (fun s : S => s • 𝟙 (Φ.obj K))) :
    Function.Surjective (fun a : R => a • 𝟙 K) := by
  intro f
  obtain ⟨s, hs⟩ := h (Φ.map f)
  exact ⟨σ s, Φ.map_injective ((hσ s K).trans hs)⟩

omit [Preadditive C] [Preadditive D] in
/-- A faithful functor reflects the vanishing of a morphism group. -/
theorem subsingleton_of_faithful (Φ : C ⥤ D) [Φ.Faithful] {X Y : C}
    (h : Subsingleton (Φ.obj X ⟶ Φ.obj Y)) : Subsingleton (X ⟶ Y) :=
  ⟨fun _ _ => Φ.map_injective (Subsingleton.elim _ _)⟩

end Transport

/-! ### The two conditions over a filtered colimit of rings -/

section Colimit

open PseudoCoherence StacksDraft.TorAmplitude

variable {R₀ : Type u} [CommRing R₀] {I : Type u} [Category.{u} I] [IsFiltered I]
  (F : I ⥤ CommAlgCat.{u} R₀) (c : Cocone F)
  (hc : IsColimit ((CommAlgCat.uliftFunctor.{u, u, u} R₀).mapCocone c))
  (A₀ : Type u) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
  [Algebra.FinitePresentation R₀ A₀]

include hc in
/-- Let `K₀` be pseudo-coherent of finite Tor dimension over `R₀`. If at every stage `i` every
endomorphism of the extension of scalars of `K₀` is a scalar multiple of the identity, then every
endomorphism of the extension of scalars of `K₀` to `A = R ⊗[R₀] A₀` is a scalar multiple of the
identity. -/
theorem surjective_smul_id_limitDerivedObj (K₀ : DerivedCategory (ModuleCat.{u} A₀))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K₀)
    (hL : HasFiniteTorDimensionCanonical R₀
      ((ModuleCat.restrictScalars (algebraMap R₀ A₀)).mapDerivedCategory.obj K₀))
    (hstage : ∀ i : I, Function.Surjective
      (fun a : stageAlgebra F A₀ i => a • 𝟙 (stageDerivedObj F A₀ i K₀))) :
    Function.Surjective (fun a : c.pt ⊗[R₀] A₀ => a • 𝟙 (limitDerivedObj c A₀ K₀)) := by
  intro ψ
  obtain ⟨i, φ, hφ⟩ := exists_stageDerivedHom F c hc A₀ K₀ K₀ hK hL ψ
  obtain ⟨a, rfl⟩ := hstage i φ
  refine ⟨stageToLimitMap c A₀ i a, ?_⟩
  rw [← hφ]
  dsimp only [stageDerivedHomComparison]
  rw [totalDerivedExtensionScalars_map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp,
    Linear.comp_smul]
  simp

include hc in
/-- Let `K₀` be pseudo-coherent and `L₀` of finite Tor dimension over `R₀`. If at every stage
there is at most one morphism between the extensions of scalars of `K₀` and `L₀`, then there is at
most one over `A = R ⊗[R₀] A₀`. -/
theorem subsingleton_limitDerivedObj (K₀ L₀ : DerivedCategory (ModuleCat.{u} A₀))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K₀)
    (hL : HasFiniteTorDimensionCanonical R₀
      ((ModuleCat.restrictScalars (algebraMap R₀ A₀)).mapDerivedCategory.obj L₀))
    (hstage : ∀ i : I, Subsingleton (stageDerivedObj F A₀ i K₀ ⟶ stageDerivedObj F A₀ i L₀)) :
    Subsingleton (limitDerivedObj c A₀ K₀ ⟶ limitDerivedObj c A₀ L₀) := by
  have key : ∀ ψ : limitDerivedObj c A₀ K₀ ⟶ limitDerivedObj c A₀ L₀, ψ = 0 := by
    intro ψ
    obtain ⟨i, φ, rfl⟩ := exists_stageDerivedHom F c hc A₀ K₀ L₀ hK hL ψ
    obtain rfl : φ = 0 := Subsingleton.elim _ _
    let := (totalDerivedExtensionScalars.{u, u, u} (stageToLimitMap c A₀ i)).additive
    simp [stageDerivedHomComparison]
  exact ⟨fun ψ ψ' => (key ψ).trans (key ψ').symm⟩

end Colimit

/-! ### A ring as the filtered colimit of its finitely generated subalgebras -/

section Subalgebras

variable (R₀ R : Type u) [CommRing R₀] [CommRing R] [Algebra R₀ R]

/-- The finitely generated `R₀`-subalgebras of `R`, ordered by inclusion. -/
abbrev FGSubalgebra : Type u := {S : Subalgebra R₀ R // S.FG}

/-- The finitely generated subalgebras are directed under inclusion. -/
instance : IsDirectedOrder (FGSubalgebra R₀ R) where
  directed S T := ⟨⟨S.1 ⊔ T.1, S.2.sup T.2⟩, le_sup_left (a := S.1), le_sup_right (a := S.1)⟩

/-- The bottom subalgebra is finitely generated. -/
instance : Nonempty (FGSubalgebra R₀ R) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

/-- The poset of finitely generated subalgebras is filtered. -/
instance : IsFiltered (FGSubalgebra R₀ R) := isFiltered_of_directed_le_nonempty _

/-- The diagram of finitely generated `R₀`-subalgebras of `R` and their inclusions. -/
def fgSubalgebraDiagram : FGSubalgebra R₀ R ⥤ CommAlgCat.{u} R₀ where
  obj S := CommAlgCat.of R₀ S.1
  map h := CommAlgCat.ofHom (Subalgebra.inclusion (leOfHom h))

/-- The cocone of inclusions of the finitely generated subalgebras into `R`. -/
def fgSubalgebraCocone : Cocone (fgSubalgebraDiagram R₀ R) where
  pt := CommAlgCat.of R₀ R
  ι := { app S := CommAlgCat.ofHom S.1.val }

/-- The subalgebra generated by one element, as a finitely generated subalgebra. -/
def fgSubalgebraOf (r : R) : FGSubalgebra R₀ R :=
  ⟨Algebra.adjoin R₀ {r}, ⟨{r}, by rw [Finset.coe_singleton]⟩⟩

/-- Every element of `R` lies in a finitely generated subalgebra. -/
theorem mem_fgSubalgebraOf (r : R) : r ∈ (fgSubalgebraOf R₀ R r).1 :=
  Algebra.subset_adjoin rfl

/-- `R` is the filtered colimit of its finitely generated `R₀`-subalgebras. -/
def fgSubalgebraCoconeIsColimit : IsColimit (fgSubalgebraCocone R₀ R) := by
  have dir : Directed (· ≤ ·) (fun S : FGSubalgebra R₀ R => S.1) :=
    fun S T => ⟨⟨S.1 ⊔ T.1, S.2.sup T.2⟩, le_sup_left (a := S.1), le_sup_right (a := S.1)⟩
  have htop : (⊤ : Subalgebra R₀ R) ≤ ⨆ S : FGSubalgebra R₀ R, S.1 := by
    intro r _
    exact (le_iSup (fun S : FGSubalgebra R₀ R => S.1) (fgSubalgebraOf R₀ R r))
      (mem_fgSubalgebraOf R₀ R r)
  let f (s : Cocone (fgSubalgebraDiagram R₀ R)) (S : FGSubalgebra R₀ R) : S.1 →ₐ[R₀] s.pt :=
    (s.ι.app S).hom
  let lift (s : Cocone (fgSubalgebraDiagram R₀ R)) : R →ₐ[R₀] s.pt :=
    (Subalgebra.iSupLift (fun S : FGSubalgebra R₀ R => S.1) dir (f s)
      (fun S T h => congrArg CommAlgCat.Hom.hom (s.w (homOfLE h)).symm) ⊤ htop).comp
      (Subalgebra.topEquiv (R := R₀) (A := R)).symm.toAlgHom
  have lift_apply (s : Cocone (fgSubalgebraDiagram R₀ R)) (S : FGSubalgebra R₀ R) (x : S.1) :
      lift s x = f s S x := by
    dsimp only [lift, AlgHom.comp_apply]
    exact Subalgebra.iSupLift_of_mem _ (Subalgebra.topEquiv.symm (x : R)) x.2
  refine
    { desc s := CommAlgCat.ofHom (lift s)
      fac s S := by
        ext x
        exact lift_apply s S x
      uniq s m hm := by
        ext r
        change m.hom r = lift s r
        rw [lift_apply s _ ⟨r, mem_fgSubalgebraOf R₀ R r⟩]
        exact congrArg (fun g => g.hom ⟨r, mem_fgSubalgebraOf R₀ R r⟩) (hm _) }

end Subalgebras

/-! ### Extension of scalars from the universe-lifted starting algebra -/

section LiftedExtension

open PseudoCoherence StacksDraft.TorAmplitude

variable {A₀ B : Type u} [CommRing A₀] [CommRing B]

/-- Restricting along `ULift A₀ ≃+* A₀` and then extending scalars along `g` composed with that
isomorphism is extending scalars along `g`. -/
def extendLiftIso (g : A₀ →+* B) (M : DerivedCategory (ModuleCat.{u} A₀)) :
    (totalDerivedExtensionScalars.{u, u, u} (g.comp (liftBaseRingHom A₀))).functor.obj
        ((baseLiftRestriction A₀).obj M) ≅
      (totalDerivedExtensionScalars.{u, u, u} g).functor.obj M :=
  ((derivedExtensionScalarsComp.{u, u} (liftBaseRingHom A₀) g).app _).symm ≪≫
    (totalDerivedExtensionScalars.{u, u, u} g).functor.mapIso
      ((totalDerivedRestrictExtendScalarsSelfIso.{u, u}
        (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀)).app M)

/-- Restricting along `ULift A₀ ≃+* A₀` and extending scalars commutes with shifts. -/
def extendLiftShiftIso (g : ULift.{u} A₀ →+* B) (M : DerivedCategory (ModuleCat.{u} A₀))
    (n : ℤ) :
    (totalDerivedExtensionScalars.{u, u, u} g).functor.obj ((baseLiftRestriction A₀).obj (M⟦n⟧)) ≅
      ((totalDerivedExtensionScalars.{u, u, u} g).functor.obj
        ((baseLiftRestriction A₀).obj M))⟦n⟧ :=
  letI := (totalDerivedExtensionScalars.{u, u, u} g).commShift
  (totalDerivedExtensionScalars.{u, u, u} g).functor.mapIso
      (((baseLiftRestriction A₀).commShiftIso n).app M) ≪≫
    ((totalDerivedExtensionScalars.{u, u, u} g).functor.commShiftIso n).app _

/-- Finite Tor dimension over the base is stable under shifts. -/
theorem hasFiniteTorDimensionCanonical_restrictScalars_shift {R₀ : Type u} [CommRing R₀]
    [Algebra R₀ A₀] (M : DerivedCategory (ModuleCat.{u} A₀)) (n : ℤ)
    (hM : HasFiniteTorDimensionCanonical R₀
      ((ModuleCat.restrictScalars (algebraMap R₀ A₀)).mapDerivedCategory.obj M)) :
    HasFiniteTorDimensionCanonical R₀
      ((ModuleCat.restrictScalars (algebraMap R₀ A₀)).mapDerivedCategory.obj (M⟦n⟧)) := by
  obtain ⟨a, b, h⟩ :=
    (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical R₀ _).1 hM
  obtain ⟨E, hflat, hGE, hLE, ⟨e⟩⟩ :=
    (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R₀ _ a b).1 h
  refine (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical R₀ _).2
    ⟨a - n, b - n, (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R₀ _ _ _).2
    ⟨E⟦n⟧, fun i => hflat (i + n), CochainComplex.isStrictlyGE_shift E a n (a - n) (by ring),
      CochainComplex.isStrictlyLE_shift E b n (b - n) (by ring), ⟨?_⟩⟩⟩
  exact (((ModuleCat.restrictScalars (algebraMap R₀ A₀)).mapDerivedCategory.commShiftIso n).app
      M) ≪≫ (shiftFunctor _ n).mapIso e ≪≫ ((DerivedCategory.Q.commShiftIso n).app E).symm

end LiftedExtension

end

end Dualizing
