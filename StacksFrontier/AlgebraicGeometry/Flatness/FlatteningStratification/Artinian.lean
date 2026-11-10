module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Artinian.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.Basic
public import StacksFrontier.RingTheory.Flat.Artinian

/-!
# Universal flattening over an Artinian base

A quasi-coherent module on a scheme over the spectrum of an Artinian ring `R` admits a
universal flattening, and the representing object is a closed subscheme of `Spec R`. Since a
closed subscheme is already a one-member stratification of its own support, the module also
admits a flattening stratification.

The argument is the one of the source. Over an Artinian ring every module has a smallest
*flattening ideal*: an ideal `I` such that the base change of the module along `R → B` is flat
exactly when `I` dies in `B` (Stacks Tag 0524, 0525). Taking the supremum over an affine open
cover of the source produces a single ideal `I` testing flatness of the whole base change, and
the closed subscheme `Spec (R ⧸ I)` then represents the flatness functor: a scheme `T` over
`Spec R` factors through it exactly when `I` dies in `Γ(T, ⊤)`, which the affine opens of `T`
detect.

## Main results

* `Module.exists_flatteningIdeal` and `Module.exists_flatteningIdeal_forall`: the flattening
  ideal of a module, and of a family of modules, over an Artinian ring.
* `AlgebraicGeometry.FlatnessSituation.exists_flatteningIdeal_of_isArtinianRing`: a single
  ideal of the Artinian base testing flatness of every base change.
* `AlgebraicGeometry.FlatnessSituation.exists_closedUniversalFlattening_of_isArtinianRing`:
  **Stacks Tag 05PB**, the universal flattening as a closed immersion.
* `AlgebraicGeometry.FlatnessSituation.hasFlatteningStratification_of_isArtinianRing`:
  **Stacks Tag 05PB**, the resulting flattening stratification.

## Implementation notes

The universal property is expressed by `CategoryTheory.Functor.RepresentableBy` for the
flatness functor on schemes over the base; since that functor is subterminal, representability
reduces to a bijection of propositions, which is
`CategoryTheory.Functor.representableBy_of_subsingleton`.

In the flattening stratification the single stratum is the whole of the closed subscheme cut out
by the kernel ideal sheaf of the representing closed immersion, and the index poset is a
one-element type.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open scoped TensorProduct

universe u v w

/-- **Stacks Project, Tag 0524 and Tag 0525, in base-change form.** A module over an Artinian
ring has a *flattening ideal*: an ideal `I` such that for every ring map `φ : R → S` the base
change `S ⊗[R] M` is flat over `S` exactly when `I` dies in `S`. -/
public theorem Module.exists_flatteningIdeal {R M : Type u} [CommRing R] [IsArtinianRing R]
    [AddCommGroup M] [Module R M] :
    ∃ I : Ideal R, ∀ {S : Type u} [CommRing S] (φ : R →+* S),
      let _ := φ.toAlgebra
      Module.Flat S (S ⊗[R] M) ↔ I.map φ = ⊥ := by
  obtain ⟨I, hI, hmin⟩ := exists_least_flat_quotient_ideal (R := R) (M := M)
  exact ⟨I, fun φ ↦ flat_tensorProduct_iff_map_least_flat_quotient_ideal_eq_bot I hI hmin φ⟩

/-- A family of modules over an Artinian ring has a common flattening ideal, namely the
supremum of the individual ones. -/
public theorem Module.exists_flatteningIdeal_forall {R : Type u} [CommRing R] [IsArtinianRing R]
    {ι : Type u} (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    ∃ I : Ideal R, ∀ {S : Type u} [CommRing S] (φ : R →+* S),
      let _ := φ.toAlgebra
      (∀ i, Module.Flat S (S ⊗[R] M i)) ↔ I.map φ = ⊥ := by
  choose J hJ using fun i ↦ Module.exists_flatteningIdeal (R := R) (M := M i)
  refine ⟨⨆ i, J i, fun {S} _ φ ↦ ?_⟩
  let _ := φ.toAlgebra
  rw [Ideal.map_iSup]
  exact ⟨fun h ↦ iSup_eq_bot.mpr fun i ↦ (hJ i φ).mp (h i),
    fun h i ↦ (hJ i φ).mpr (iSup_eq_bot.mp h i)⟩

namespace CategoryTheory.Functor

/-- A functor with subsingleton values is represented by an object `Y` as soon as every hom
into `Y` is unique and the values of the functor are nonempty exactly where the homs into `Y`
are. -/
public noncomputable def representableBy_of_subsingleton {C : Type u} [Category.{v, u} C]
    (F : Cᵒᵖ ⥤ Type w) (Y : C) (hF : ∀ X, Subsingleton (F.obj (Opposite.op X)))
    (hHom : ∀ X, Subsingleton (X ⟶ Y))
    (h : ∀ X, Nonempty (F.obj (Opposite.op X)) ↔ Nonempty (X ⟶ Y)) : F.RepresentableBy Y where
  homEquiv {X} :=
    { toFun := fun f ↦ Classical.choice ((h X).2 ⟨f⟩)
      invFun := fun x ↦ Classical.choice ((h X).1 ⟨x⟩)
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _ }
  homEquiv_comp {X _} _ _ := @Subsingleton.elim (F.obj (Opposite.op X)) (hF X) _ _

end CategoryTheory.Functor

namespace AlgebraicGeometry.FlatnessSituation

/-- The flatness functor is represented by an object `W` of `Over S` as soon as the homs into
`W` are unique and exist exactly where the base change is flat. -/
public theorem nonempty_flatFunctor_representableBy {D : FlatnessSituation.{u}} (W : Over D.S)
    (hHom : ∀ T : Over D.S, Subsingleton (T ⟶ W))
    (hiff : ∀ T : Over D.S, D.IsFlatAfterBaseChange T ↔ Nonempty (T ⟶ W)) :
    Nonempty (D.flatFunctor.RepresentableBy W) :=
  ⟨Functor.representableBy_of_subsingleton D.flatFunctor W
    (fun T ↦ D.flatFunctor_obj_subsingleton (Opposite.op T)) hHom
    fun T ↦ (D.flatFunctor_obj_nonempty_iff T).trans (hiff T)⟩

/-- **Stacks Project, Tag 05PB, the flattening ideal of the situation.** For a quasi-coherent
module on a scheme over the spectrum of an Artinian ring there is a single ideal `I` of that
ring such that the base change of the module along `Spec B → Spec R` is flat over `Spec B`
exactly when `I` dies in `B`. -/
public theorem exists_flatteningIdeal_of_isArtinianRing (R : CommRingCat.{u}) [IsArtinianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec R) (F : X.Modules) [F.IsQuasicoherent] :
    ∃ I : Ideal R, ∀ (B : CommRingCat.{u}) (φ : R ⟶ B),
      IsFlatOver (pullback.snd f (Spec.map φ)).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map φ))).obj F) ↔ I.map φ.hom = ⊥ := by
  let 𝒰 := X.affineOpenCover
  let α (i : 𝒰.I₀) : R ⟶ 𝒰.X i := Spec.preimage (𝒰.f i ≫ f)
  let M (i : 𝒰.I₀) : ModuleCat R :=
    (ModuleCat.restrictScalars (α i).hom).obj
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (𝒰.f i)).obj F))
  obtain ⟨I, hI⟩ := Module.exists_flatteningIdeal_forall (R := R) fun i ↦ (M i : Type u)
  refine ⟨I, fun B φ ↦ ?_⟩
  let _ : Algebra R B := φ.hom.toAlgebra
  refine (isFlatOver_baseChange_iff_openCover f (Spec.map φ) F 𝒰.openCover).trans
    (Iff.trans (forall_congr' fun i ↦ ?_) (hI φ.hom))
  have hα : Spec.map (α i) = 𝒰.f i ≫ f := Spec.map_preimage _
  change IsFlatOver (pullback.snd (𝒰.f i ≫ f) (Spec.map φ)).toLRSHom.toShHom
    ((Scheme.Modules.pullback (pullback.fst (𝒰.f i ≫ f) (Spec.map φ))).obj
      ((Scheme.Modules.pullback (𝒰.f i)).obj F)) ↔ _
  rw [← hα]
  exact isFlatOver_affine_baseChange_iff (α i) φ ((Scheme.Modules.pullback (𝒰.f i)).obj F)

end AlgebraicGeometry.FlatnessSituation

namespace AlgebraicGeometry

/-- A morphism to the spectrum of a ring whose global comorphism kills an ideal factors through
the spectrum of the quotient by that ideal. -/
public theorem exists_lift_specMap_quotientMk {R : Type u} [CommRing R] {T : Scheme.{u}}
    (g : T ⟶ Spec (.of R)) (I : Ideal R)
    (h : I ≤ RingHom.ker (((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop).hom)) :
    ∃ l : T ⟶ Spec (.of (R ⧸ I)),
      l ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g := by
  let ψ := (Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop
  let l : CommRingCat.of (R ⧸ I) ⟶ Γ(T, ⊤) :=
    CommRingCat.ofHom (Ideal.Quotient.lift I ψ.hom h)
  refine ⟨T.toSpecΓ ≫ Spec.map l, ?_⟩
  rw [Category.assoc, ← Spec.map_comp,
    show CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ l = ψ by ext; rfl]
  dsimp only [ψ]
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- An ideal of `R` that dies on every chart of the affine open cover of a scheme over
`Spec R` dies in the global sections. -/
public theorem le_ker_appTop_of_forall_affineOpenCover {R : Type u} [CommRing R]
    {T : Scheme.{u}} (g : T ⟶ Spec (.of R)) (I : Ideal R)
    (h : ∀ i, I.map (Spec.preimage (T.affineOpenCover.f i ≫ g)).hom = ⊥) :
    I ≤ RingHom.ker (((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop).hom) := by
  let ψ : CommRingCat.of R ⟶ Γ(T, ⊤) := (Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop
  intro r hr
  change ψ r = 0
  refine T.affineOpenCover.openCover.ext_elem _ _ fun i ↦ ?_
  let k := T.affineOpenCover.f i
  let α : CommRingCat.of R ⟶ T.affineOpenCover.X i := Spec.preimage (k ≫ g)
  have hα : Spec.map α = k ≫ g := Spec.map_preimage _
  have hrzero : α r = 0 := (Ideal.map_eq_bot_iff_le_ker α.hom).mp (h i) hr
  have hn : α ≫ (Scheme.ΓSpecIso _).inv = ψ ≫ k.appTop := by
    rw [Scheme.ΓSpecIso_inv_naturality, hα, Scheme.Hom.comp_appTop]
    rfl
  have he := ConcreteCategory.congr_hom hn r
  change k.appTop (ψ r) = k.appTop 0
  change (Scheme.ΓSpecIso _).inv (α r) = k.appTop (ψ r) at he
  simpa only [hrzero, map_zero] using he.symm

namespace FlatnessSituation

/-- A morphism representing the flatness functor is surjective: the base change of the module
to the residue field of any point of the base is flat, so that point is in the image. -/
public theorem surjective_hom_of_flatFunctor_representableBy {D : FlatnessSituation.{u}}
    {W : Over D.S} (e : D.flatFunctor.RepresentableBy W) : Function.Surjective W.hom := by
  intro s
  let T : Over D.S := Over.mk (D.S.fromSpecResidueField s)
  let g : T ⟶ W :=
    e.homEquiv.symm ⟨isFlatOver_of_isField (pullback.snd D.f T.hom) (D.baseChangeModule T)⟩
  refine ⟨g.left (IsLocalRing.closedPoint (D.S.residueField s)), ?_⟩
  have h := congrArg (fun k : T.left ⟶ D.S ↦ k (IsLocalRing.closedPoint (D.S.residueField s)))
    (Over.w g)
  change W.hom (g.left _) = (D.S.fromSpecResidueField s) _ at h
  exact h.trans (D.S.fromSpecResidueField_apply s _)

/-- A flatness functor represented by a closed immersion gives a flattening stratification: the
closed subscheme cut out by the kernel ideal sheaf is a single stratum covering the base. -/
public theorem hasFlatteningStratification_of_isClosedImmersion {D : FlatnessSituation.{u}}
    (W : Over D.S) [IsClosedImmersion W.hom] (e : D.flatFunctor.RepresentableBy W) :
    D.HasFlatteningStratification := by
  classical
  let J := W.hom.ker
  let U : J.subscheme.Opens := ⊤
  let Y : PUnit.{u + 1} → Scheme.{u} := fun _ ↦ U.toScheme
  let g : ∀ i, Y i ⟶ D.S := fun _ ↦ U.ι ≫ J.subschemeι
  have : IsIso U.ι := J.subscheme.topIso.isIso_hom
  let a : W.left ≅ U.toScheme := asIso W.hom.toImage ≪≫ (asIso U.ι).symm
  let b : W.left ≅ ∐ Y := a ≪≫ (coproductUniqueIso Y).symm
  refine ⟨PUnit.{u + 1}, inferInstance, (fun _ ↦ J), ?_, ?_, ?_, (fun _ ↦ U), ?_, W, b,
    inferInstance, ?_, ⟨e⟩⟩
  · simpa only [Set.iUnion_const] using Set.eq_univ_of_forall fun s ↦
      W.hom.range_subset_ker_support (surjective_hom_of_flatFunctor_representableBy e s)
  · exact locallyFinite_of_finite _
  · intro i j
    simp
  · intro i
    change Set.range (J.subschemeι ∘ U.ι) = _
    rw [Set.range_comp, (Scheme.Hom.surjective U.ι).range_eq, Set.image_univ,
      J.range_subschemeι]
    simp
  · change W.hom = a.hom ≫ (coproductUniqueIso Y).inv ≫ Sigma.desc g
    rw [coproductUniqueIso_inv, Sigma.ι_comp_desc]
    dsimp only [a, g]
    rw [Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, Category.assoc,
      IsIso.inv_hom_id_assoc]
    exact W.hom.toImage_imageι.symm

/-- **Stacks Project, Tag 05PB.** A quasi-coherent module on a scheme over the spectrum of an
Artinian ring admits a universal flattening, and the representing morphism is a closed
immersion. -/
@[stacks 05PB "the closed universal flattening", sga "6 XII 4.5" "special case"]
public theorem exists_closedUniversalFlattening_of_isArtinianRing {R : Type u} [CommRing R]
    [IsArtinianRing R] (D : FlatnessSituation.{u}) (hS : D.S = Spec (.of R)) :
    ∃ W : Over D.S, IsClosedImmersion W.hom ∧ Nonempty (D.flatFunctor.RepresentableBy W) := by
  classical
  obtain ⟨S, X, f, F⟩ := D
  rename_i hF
  have : (show X.Modules from F).IsQuasicoherent := hF
  dsimp only at hS
  subst S
  let D : FlatnessSituation.{u} := { S := Spec (.of R), X := X, f := f, F := F }
  change ∃ W : Over D.S, _
  obtain ⟨I, hI⟩ := exists_flatteningIdeal_of_isArtinianRing (.of R) f F
  let q : CommRingCat.of R ⟶ .of (R ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let W : Over D.S := Over.mk (Spec.map q)
  have hclosed : IsClosedImmersion (Spec.map q) :=
    IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
  refine ⟨W, hclosed, nonempty_flatFunctor_representableBy W ?_ ?_⟩
  · intro T
    have _ : Mono W.hom := inferInstanceAs (Mono (Spec.map q))
    exact ⟨fun a b ↦ Over.OverMorphism.ext ((cancel_mono W.hom).mp
      ((Over.w a).trans (Over.w b).symm))⟩
  · intro T
    refine ⟨fun hT ↦ ?_, fun ⟨l⟩ ↦ D.isFlatAfterBaseChange_of_hom l
      ((hI (.of (R ⧸ I)) q).mpr (Ideal.map_quotient_self I))⟩
    obtain ⟨l, hl⟩ := exists_lift_specMap_quotientMk T.hom I
      (le_ker_appTop_of_forall_affineOpenCover T.hom I fun i ↦ (hI _ _).mp (by
        rw [Spec.map_preimage]
        exact D.isFlatAfterBaseChange_of_hom
          (Over.homMk _ rfl : Over.mk (T.left.affineOpenCover.f i ≫ T.hom) ⟶ T) hT))
    exact ⟨Over.homMk l hl⟩

/-- **Stacks Project, Tag 05PB.** A quasi-coherent module on a scheme over the spectrum of an
Artinian ring has a flattening stratification. -/
@[stacks 05PB "the flattening stratification", sga "6 XII 4.5" "special case"]
public theorem hasFlatteningStratification_of_isArtinianRing {R : Type u} [CommRing R]
    [IsArtinianRing R] (D : FlatnessSituation.{u}) (hS : D.S = Spec (.of R)) :
    D.HasFlatteningStratification := by
  obtain ⟨W, _, ⟨e⟩⟩ := exists_closedUniversalFlattening_of_isArtinianRing D hS
  exact hasFlatteningStratification_of_isClosedImmersion W e

end FlatnessSituation

end AlgebraicGeometry
