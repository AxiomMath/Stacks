module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.VanishingAfterBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.AffineTestReduction
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.AffineChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSections
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The isomorphism locus of a surjection with projective sections

Let `f : X ⟶ S` be a morphism of affine schemes and let `u : F ⟶ G` be a surjection of
quasi-coherent modules on `X` whose source has projective module of global sections over
`Γ(S, 𝒪_S)`.  Then the locus on which `u` becomes an isomorphism after base change is cut out by a
closed subscheme of `S`: the functor
`Stacks.Flatness.ModuleMapBaseChangeSituation.isomorphismFunctor` is represented by a closed
immersion into `S`.

This is the affine case in which the devissage of
[Stacks, Tag 05PF](https://stacks.math.columbia.edu/tag/05PF) terminates, and the construction of
the closed subscheme is Tag 05PE: a surjection out of a projective module has an ideal of the base
ring which, after every base change, vanishes exactly when the map becomes bijective.

Three steps translate that algebraic statement into the geometric one.

*The direct image.*  For a morphism `f : X ⟶ S` with `X` affine, invertibility of a homomorphism
of quasi-coherent modules on `X` is equivalent to invertibility of its direct image, since the
direct image is tested on global sections and over an affine scheme a homomorphism is invertible
exactly when it is on global sections.  Affine base change — Tag 02KG, in the form
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom` —
identifies the inverse image of the direct image along a base change with the direct image of the
inverse image, so the isomorphism condition over `Spec B` becomes invertibility of an inverse
image on `S` of a single homomorphism of quasi-coherent modules on `S`.

*The dictionary with modules.*  Over an affine scheme a homomorphism of quasi-coherent modules is
the associated sheaf of its homomorphism of modules of global sections, and the inverse image
along `Spec φ` of an associated sheaf is the associated sheaf of the extension of scalars along
`φ` (Tag 01I9).  So the isomorphism condition over `Spec B` is bijectivity of an extension of
scalars, which is what Tag 05PE controls.

*Affine test schemes suffice.*  An ideal of the base ring cutting out the locus on the spectra of
its algebras cuts it out on every scheme over `S`, by
`Stacks.Flatness.ModuleMapBaseChangeSituation.isoFactorizationCriterion_of_affineTests`.

## Main results

* `Stacks.Flatness.ModuleMapBaseChangeSituation.isoFactorizationCriterion_of_specTests`: spectra
  of rings suffice as test schemes for the factorization criterion.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.exists_ideal_isIso_pullback_iff`: an ideal of the
  base ring cutting out the locus, for a surjection of quasi-coherent modules on an affine scheme
  with projective module of global sections.
* `Stacks.Flatness.isomorphismFunctor_representableBy_closedImmersion_of_projective_sections`: the
  first assertion of Tag 05PF in the affine case with projective sections.

## Implementation notes

The hypothesis that the module of global sections of `F` be projective over `Γ(S, 𝒪_S)` is stated
for the scalar action obtained by restricting along `f`, which is the action
`Module.compHom Γ(F, ⊤) f.appTop.hom`; it is transported to the action through
`moduleSpecΓFunctor` on the direct image, where the two actions differ only by the canonical
identification `Scheme.ΓSpecIso`, by `Module.Projective.of_equiv`.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 05PE](https://stacks.math.columbia.edu/tag/05PE)
* [Stacks Project, Tag 05PF](https://stacks.math.columbia.edu/tag/05PF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace CategoryTheory

/-- In a natural transformation which is invertible at the two objects of a morphism, the two
images of that morphism are invertible together. -/
theorem isIso_map_iff_of_isIso_app {C E : Type*} [Category C] [Category E] {L R : C ⥤ E}
    (α : L ⟶ R) {M N : C} (φ : M ⟶ N) (hM : IsIso (α.app M)) (hN : IsIso (α.app N)) :
    IsIso (L.map φ) ↔ IsIso (R.map φ) :=
  isIso_iff_of_sq_of_isIso hM hN (α.naturality φ).symm

end CategoryTheory

namespace AlgebraicGeometry

/-- **Affine base change for the isomorphism condition.**  In a cartesian square whose right-hand
morphism is affine, the inverse image along the base change of the direct image of a homomorphism
of quasi-coherent modules is invertible exactly when the direct image of its inverse image is.
This is Tag 02KG applied at the source and the target of the homomorphism. -/
theorem isIso_pullback_pushforward_iff {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (hw : IsPullback g' f' f g) [IsAffineHom f] {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    IsIso ((Scheme.Modules.pullback g).map ((Scheme.Modules.pushforward f).map φ)) ↔
      IsIso ((Scheme.Modules.pushforward f').map ((Scheme.Modules.pullback g').map φ)) :=
  isIso_map_iff_of_isIso_app (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hw.w)
    φ (Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hw F)
    (Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hw G)

/-- A surjection of quasi-coherent modules on the spectrum of a ring is surjective on modules of
global sections: the counit of the associated-sheaf adjunction is invertible at a quasi-coherent
module, so the associated sheaf of the homomorphism of global sections is the homomorphism up to
isomorphism, and the associated-sheaf functor reflects epimorphisms. -/
theorem epi_moduleSpecΓ_map {A : CommRingCat.{u}} {F G : (Spec A).Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) [Epi φ] :
    Epi (moduleSpecΓFunctor.map φ) := by
  have : IsIso ((tilde.adjunction (R := A)).counit.app F) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F
  have : IsIso ((tilde.adjunction (R := A)).counit.app G) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G
  have heq : (tilde.functor A).map (moduleSpecΓFunctor.map φ) =
      (tilde.adjunction (R := A)).counit.app F ≫ φ ≫
        inv ((tilde.adjunction (R := A)).counit.app G) := by
    rw [← cancel_mono ((tilde.adjunction (R := A)).counit.app G)]
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Functor.comp_map,
      Functor.id_map] using (tilde.adjunction (R := A)).counit.naturality φ
  have : Epi ((tilde.functor A).map (moduleSpecΓFunctor.map φ)) := by
    rw [heq]; infer_instance
  exact (tilde.functor A).epi_of_epi_map inferInstance

/-- Over the spectrum of a ring a homomorphism of quasi-coherent modules is invertible exactly
when its homomorphism of modules of global sections is. -/
theorem isIso_iff_isIso_moduleSpecΓ_map {A : CommRingCat.{u}} {F G : (Spec A).Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    IsIso φ ↔ IsIso (moduleSpecΓFunctor.map φ) :=
  (isIso_map_iff_of_isIso_app (tilde.adjunction (R := A)).counit φ
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F)
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G)).symm.trans
    (isIso_iff_of_reflects_iso _ (tilde.functor A))

/-- An inverse image of a homomorphism of quasi-coherent modules on the spectrum of a ring is
invertible exactly when the inverse image of the associated sheaf of its homomorphism of modules
of global sections is. -/
theorem isIso_pullback_iff_isIso_pullback_tilde_sections {A : CommRingCat.{u}} {T : Scheme.{u}}
    (q : T ⟶ Spec A) {F G : (Spec A).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) :
    IsIso ((Scheme.Modules.pullback q).map φ) ↔
      IsIso ((Scheme.Modules.pullback q).map
        ((tilde.functor A).map (moduleSpecΓFunctor.map φ))) := by
  have : IsIso ((tilde.adjunction (R := A)).counit.app F) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F
  have : IsIso ((tilde.adjunction (R := A)).counit.app G) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G
  exact (isIso_map_iff_of_isIso_app
    (Functor.whiskerRight (tilde.adjunction (R := A)).counit (Scheme.Modules.pullback q)) φ
    (Functor.map_isIso _ _) (Functor.map_isIso _ _)).symm

/-- The inverse image along the morphism of spectra induced by a ring map of the associated sheaf
of a homomorphism of modules is invertible exactly when the extension of scalars of that
homomorphism is.  This is Tag 01I9 together with the fact that the associated-sheaf functor
reflects isomorphisms. -/
theorem isIso_tilde_pullback_iff_isIso_extendScalars {A B : CommRingCat.{u}} (φ : A ⟶ B)
    {M N : ModuleCat.{u} A} (v : M ⟶ N) :
    IsIso ((Scheme.Modules.pullback (Spec.map φ)).map ((tilde.functor A).map v)) ↔
      IsIso ((ModuleCat.extendScalars φ.hom).map v) :=
  (NatIso.isIso_map_iff (pullbackTildeIso A B φ) v).trans
    (isIso_iff_of_reflects_iso _ (tilde.functor B))

end AlgebraicGeometry

namespace Module

/-- Tensoring a linear map on the left and on the right are bijective together: the commutativity
isomorphism of the tensor product exchanges them. -/
theorem bijective_lTensor_iff_bijective_rTensor {A : Type*} [CommRing A] {M N B : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [AddCommGroup B] [Module A B]
    (v : M →ₗ[A] N) :
    Function.Bijective (v.lTensor B) ↔ Function.Bijective (v.rTensor B) := by
  have h : (v.lTensor B) ∘ (TensorProduct.comm A M B) =
      (TensorProduct.comm A N B) ∘ (v.rTensor B) := by
    funext x
    exact LinearMap.lTensor_comm v x
  rw [← (TensorProduct.comm A M B).toEquiv.bijective_comp]
  change Function.Bijective ((v.lTensor B) ∘ (TensorProduct.comm A M B)) ↔ _
  rw [h]
  exact Equiv.comp_bijective _ (TensorProduct.comm A N B).toEquiv

end Module

namespace AlgebraicGeometry

/-- **Tag 05PE in the language of associated sheaves.**  For a surjection of modules over a ring
whose source is projective there is an ideal of that ring which, for every ring map out of it,
vanishes in the target exactly when the inverse image of the associated sheaf of the surjection
along the induced morphism of spectra is invertible. -/
theorem exists_ideal_isIso_tilde_pullback_iff (A : CommRingCat.{u}) (M N : ModuleCat.{u} A)
    (v : M ⟶ N) (hv : Function.Surjective v.hom) [Module.Projective A M] :
    ∃ I : Ideal A, ∀ (B : CommRingCat.{u}) (φ : A ⟶ B),
      IsIso ((Scheme.Modules.pullback (Spec.map φ)).map ((tilde.functor A).map v)) ↔
        Ideal.map φ.hom I = ⊥ := by
  obtain ⟨I, hI⟩ := Module.exists_ideal_bijective_rTensor_iff_map_eq_bot A M N v.hom hv
  refine ⟨I, fun B φ ↦ ?_⟩
  let _ : Algebra A B := φ.hom.toAlgebra
  rw [isIso_tilde_pullback_iff_isIso_extendScalars, ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (v.hom.lTensor B) ↔ _
  rw [Module.bijective_lTensor_iff_bijective_rTensor]
  exact hI B

/-- **Tag 05PE for quasi-coherent modules on the spectrum of a ring.**  For a surjection of
quasi-coherent modules on `Spec A` whose source has projective module of global sections there is
an ideal of `A` which, for every ring map out of `A`, vanishes in the target exactly when the
inverse image of the surjection along the induced morphism of spectra is invertible. -/
theorem exists_ideal_isIso_pullback_iff (A : CommRingCat.{u}) {F G : (Spec A).Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G)
    (hφ : Function.Surjective (moduleSpecΓFunctor.map φ).hom)
    [Module.Projective A (moduleSpecΓFunctor.obj F)] :
    ∃ I : Ideal A, ∀ (B : CommRingCat.{u}) (ψ : A ⟶ B),
      IsIso ((Scheme.Modules.pullback (Spec.map ψ)).map φ) ↔ Ideal.map ψ.hom I = ⊥ := by
  obtain ⟨I, hI⟩ := exists_ideal_isIso_tilde_pullback_iff A (moduleSpecΓFunctor.obj F)
    (moduleSpecΓFunctor.obj G) (moduleSpecΓFunctor.map φ) hφ
  refine ⟨I, fun B ψ ↦ ?_⟩
  rw [isIso_pullback_iff_isIso_pullback_tilde_sections]
  exact hI B ψ

/-- The direct image along the isomorphism of an affine scheme with the spectrum of its ring of
global sections is an equivalence. -/
private theorem isEquivalence_pushforward_isoSpec (X : Scheme.{u}) [IsAffine X] :
    (Scheme.Modules.pushforward X.isoSpec.hom).IsEquivalence :=
  (_root_.AlgebraicGeometry.Scheme.Modules.pushforwardEquivOfIso X.isoSpec).isEquivalence_functor

/-- On an affine scheme a homomorphism of quasi-coherent modules is invertible exactly when it is
invertible on global sections. -/
theorem isIso_iff_isIso_appTop_of_isAffine {X : Scheme.{u}} [IsAffine X] {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) : IsIso φ ↔ IsIso (φ.app ⊤) := by
  have := isEquivalence_pushforward_isoSpec X
  rw [← isIso_iff_of_reflects_iso φ (Scheme.Modules.pushforward X.isoSpec.hom),
    isIso_iff_isIso_moduleSpecΓ_map, ConcreteCategory.isIso_iff_bijective,
    ConcreteCategory.isIso_iff_bijective]
  rfl

/-- On an affine scheme a surjection of quasi-coherent modules is surjective on global
sections. -/
theorem epi_appTop_of_isAffine {X : Scheme.{u}} [IsAffine X] {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) [Epi φ] : Epi (φ.app ⊤) := by
  have := isEquivalence_pushforward_isoSpec X
  have := epi_moduleSpecΓ_map ((Scheme.Modules.pushforward X.isoSpec.hom).map φ)
  rw [AddCommGrpCat.epi_iff_surjective]
  exact (ModuleCat.epi_iff_surjective
    (moduleSpecΓFunctor.map ((Scheme.Modules.pushforward X.isoSpec.hom).map φ))).mp inferInstance

/-- For a morphism out of an affine scheme a homomorphism of quasi-coherent modules is invertible
exactly when its direct image is: the direct image is tested on global sections, and on an affine
scheme global sections detect invertibility. -/
theorem isIso_iff_isIso_pushforward_of_isAffine {X S : Scheme.{u}} [IsAffine X] (f : X ⟶ S)
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    IsIso φ ↔ IsIso ((Scheme.Modules.pushforward f).map φ) := by
  refine ⟨fun h ↦ Functor.map_isIso _ _, fun h ↦ ?_⟩
  refine (isIso_iff_isIso_appTop_of_isAffine φ).mpr ?_
  exact Scheme.Modules.Hom.isIso_iff_isIso_app.mp h ⊤

end AlgebraicGeometry

namespace Stacks.Flatness.ModuleMapBaseChangeSituation

variable (D : ModuleMapBaseChangeSituation.{u})

/-- **Spectra of rings suffice as test schemes for the factorization criterion.**  Every affine
scheme over the base is isomorphic over the base to the spectrum of its ring of global
sections. -/
theorem isoFactorizationCriterion_of_specTests {Z : Scheme.{u}} (i : Z ⟶ D.S) (hi : Mono i)
    (h : ∀ (B : CommRingCat.{u}) (q : Spec B ⟶ D.S),
      D.IsIsomorphismAfterBaseChange (Over.mk q) ↔ ∃ g : Spec B ⟶ Z, g ≫ i = q) :
    D.IsoFactorizationCriterion i := by
  refine D.isoFactorizationCriterion_of_affineTests i hi fun T hT ↦ ?_
  have := hT
  set q : Spec Γ(T.left, ⊤) ⟶ D.S := T.left.isoSpec.inv ≫ T.hom with hq
  have he : (Over.isoMk T.left.isoSpec (by simp [hq]) : T ≅ Over.mk q).hom.left =
      T.left.isoSpec.hom := rfl
  set e : T ≅ Over.mk q := Over.isoMk T.left.isoSpec (by simp [hq]) with hedef
  rw [show D.IsIsomorphismAfterBaseChange T ↔ D.IsIsomorphismAfterBaseChange (Over.mk q) from
      ⟨D.isIsomorphismAfterBaseChange_of_hom e.inv,
        D.isIsomorphismAfterBaseChange_of_hom e.hom⟩,
    h]
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨T.left.isoSpec.hom ≫ g, ?_⟩, fun ⟨g, hg⟩ ↦
    ⟨T.left.isoSpec.inv ≫ g, ?_⟩⟩
  · rw [Category.assoc, hg, hq, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · rw [Category.assoc, hg, hq]

/-- **The isomorphism condition over the spectrum of an algebra, in terms of the direct image.**
For a situation with affine source and affine base, with the base identified with `Spec A`, the
base change of `u` to `Spec B` is an isomorphism exactly when the inverse image along `Spec φ` of
the direct image of `u` to `Spec A` is. -/
theorem isIsomorphismAfterBaseChange_iff_pullback_pushforward [IsAffine D.X] [IsAffine D.S]
    (A : CommRingCat.{u}) (e : D.S ≅ Spec A) (B : CommRingCat.{u}) (φ : A ⟶ B) :
    D.IsIsomorphismAfterBaseChange (Over.mk (Spec.map φ ≫ e.inv)) ↔
      IsIso ((Scheme.Modules.pullback (Spec.map φ)).map
        ((Scheme.Modules.pushforward (D.f ≫ e.hom)).map D.hom)) := by
  have hs : IsPullback (pullback.fst D.f (Spec.map φ ≫ e.inv))
      (pullback.snd D.f (Spec.map φ ≫ e.inv)) (D.f ≫ e.hom) (Spec.map φ) :=
    (IsPullback.of_hasPullback D.f (Spec.map φ ≫ e.inv)).of_iso (Iso.refl _) (Iso.refl _)
      (Iso.refl _) e (by simp) (by simp) (by simp) (by simp)
  exact (isIso_iff_isIso_pushforward_of_isAffine (pullback.snd D.f (Spec.map φ ≫ e.inv))
    ((Scheme.Modules.pullback (pullback.fst D.f (Spec.map φ ≫ e.inv))).map D.hom)).trans
      (isIso_pullback_pushforward_iff hs D.hom).symm

/-- A morphism from the spectrum of a ring to the spectrum of another factors through the
spectrum of a quotient exactly when the ideal maps to zero. -/
theorem spec_quotient_exists_comp_eq_iff {A B : CommRingCat.{u}} (φ : A ⟶ B) (I : Ideal A) :
    (∃ g : Spec B ⟶ Spec (CommRingCat.of (A ⧸ I)),
        g ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = Spec.map φ) ↔
      Ideal.map φ.hom I = ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker]
  constructor
  · rintro ⟨g, hg⟩ a ha
    have heq : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ Spec.preimage g = φ :=
      Spec.map_injective (by simpa using hg)
    subst heq
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  · intro hle
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I φ.hom hle)), ?_⟩
    rw [← Spec.map_comp]
    rfl

/-- **An ideal of the base ring cutting out the isomorphism locus gives the representing closed
immersion.**  With the base identified with `Spec A`, an ideal `I` of `A` whose image vanishes in
`B` exactly when the base change of `u` to `Spec B` is an isomorphism makes `Spec (A ⧸ I)` the
representing object: a morphism to `Spec A` factors through `Spec (A ⧸ I)` exactly when `I` dies
on it, and spectra of rings suffice as test schemes. -/
theorem exists_closedImmersion_representableBy_of_specIdealCriterion
    (A : CommRingCat.{u}) (e : D.S ≅ Spec A) (I : Ideal A)
    (h : ∀ (B : CommRingCat.{u}) (φ : A ⟶ B),
      D.IsIsomorphismAfterBaseChange (Over.mk (Spec.map φ ≫ e.inv)) ↔ Ideal.map φ.hom I = ⊥) :
    ∃ W : Over D.S, IsClosedImmersion W.hom ∧
      Nonempty (D.isomorphismFunctor.RepresentableBy W) := by
  let q : Spec (CommRingCat.of (A ⧸ I)) ⟶ Spec A :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion (q ≫ e.inv) := IsClosedImmersion.comp _ _
  refine ⟨Over.mk (q ≫ e.inv), inferInstanceAs (IsClosedImmersion (q ≫ e.inv)),
    ⟨D.representableByOfIsoFactorizationCriterion
    (q ≫ e.inv) inferInstance (D.isoFactorizationCriterion_of_specTests (q ≫ e.inv)
      inferInstance fun B r ↦ ?_)⟩⟩
  have hr : Spec.map (Spec.preimage (r ≫ e.hom)) ≫ e.inv = r := by simp
  rw [← hr, h B (Spec.preimage (r ≫ e.hom)),
    ← spec_quotient_exists_comp_eq_iff (Spec.preimage (r ≫ e.hom)) I]
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨g, ?_⟩, fun ⟨g, hg⟩ ↦ ⟨g, ?_⟩⟩
  · rw [← Category.assoc, hg]
  · exact (cancel_mono e.inv).mp (by rw [Category.assoc]; exact hg)

/-- **The isomorphism functor of a surjection with projective direct image is represented by a
closed immersion.**  For a situation with affine source and affine base, with the base identified
with `Spec A`, the ideal of Tag 05PE attached to the direct image of `u` cuts out the isomorphism
locus on the spectra of `A`-algebras, and spectra suffice as test schemes. -/
@[sga "3 VIB 6.2.3" "(i), special case"]
theorem exists_closedImmersion_representableBy_of_projective_pushforward [IsAffine D.X]
    [IsAffine D.S] [Epi D.hom] (A : CommRingCat.{u}) (e : D.S ≅ Spec A)
    [Module.Projective A (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pushforward (D.f ≫ e.hom)).obj D.F))] :
    ∃ W : Over D.S, IsClosedImmersion W.hom ∧
      Nonempty (D.isomorphismFunctor.RepresentableBy W) := by
  have hsurj : Function.Surjective (moduleSpecΓFunctor.map
      ((Scheme.Modules.pushforward (D.f ≫ e.hom)).map D.hom)).hom := by
    exact (AddCommGrpCat.epi_iff_surjective _).mp (epi_appTop_of_isAffine D.hom)
  obtain ⟨I, hI⟩ := exists_ideal_isIso_pullback_iff A
    ((Scheme.Modules.pushforward (D.f ≫ e.hom)).map D.hom) hsurj
  refine D.exists_closedImmersion_representableBy_of_specIdealCriterion A e I fun B φ ↦ ?_
  exact (D.isIsomorphismAfterBaseChange_iff_pullback_pushforward A e B φ).trans (hI B φ)

end Stacks.Flatness.ModuleMapBaseChangeSituation

namespace AlgebraicGeometry

/-- Projectivity of the module of global sections of a module over the ring of global sections of
an affine base, for the action obtained by restricting along the structure morphism, is
projectivity of the module of global sections of its direct image to the spectrum of that ring:
the two modules have the same elements and the two actions differ by the canonical identification
of a ring with the global sections of its spectrum. -/
theorem projective_moduleSpecΓ_pushforward {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    (F : X.Modules)
    (h : letI : Module Γ(S, ⊤) Γ(F, ⊤) := Module.compHom Γ(F, ⊤) f.appTop.hom
      Module.Projective Γ(S, ⊤) Γ(F, ⊤)) :
    Module.Projective Γ(S, ⊤) (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pushforward (f ≫ S.isoSpec.hom)).obj F)) := by
  let _ : Module Γ(S, ⊤) Γ(F, ⊤) := Module.compHom Γ(F, ⊤) f.appTop.hom
  let _ := h
  let v : Γ(F, ⊤) ≃ₗ[Γ(S, ⊤)] moduleSpecΓFunctor.obj
      ((Scheme.Modules.pushforward (f ≫ S.isoSpec.hom)).obj F) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro a m
        change f.appTop.hom a • m =
          (((Scheme.ΓSpecIso Γ(S, ⊤)).inv ≫ (f ≫ S.isoSpec.hom).appTop).hom a) • m
        simp [Scheme.isoSpec, Scheme.toSpecΓ_appTop] }
  exact Module.Projective.of_equiv v

end AlgebraicGeometry

namespace Stacks.Flatness

/-- **Stacks Project, Tag 05PF.** The isomorphism-after-base-change functor of a surjection
`u : F ⟶ G` of quasi-coherent modules on an affine scheme `X` over an affine base `S`, whose
source has projective module of global sections over `Γ(S, 𝒪_S)`, is represented by a closed
immersion `Z ⟶ S`.

This is the situation in which the devissage of the source's proof terminates: the representing
closed subscheme is cut out by the ideal of `Γ(S, 𝒪_S)` supplied by Tag 05PE, which after every
base change vanishes exactly when `u` becomes an isomorphism.  The hypotheses of the source — that
`f` and `F` be of finite presentation and that `F` be flat and pure relative to `S` — are what the
source's étale localization uses to reduce the general case to this one; they are not needed once
the situation is affine with projective sections, and are therefore absent here. -/
@[stacks 05PF "representability by a closed immersion, for an affine situation whose source \
module has projective global sections: this is the terminal case of the source's devissage, \
Step 4 of its proof together with Tag 05PE. The étale localization of Steps 1-3, which reduces \
the general case to this one, is \
`Stacks.Flatness.exists_closedImmersion_representableBy_isomorphismFunctor`",
  sga "3 VIB 6.2.3" "(i), special case",
  sga "3 VIII 6.4" "special case"]
theorem isomorphismFunctor_representableBy_closedImmersion_of_projective_sections
    (D : ModuleMapBaseChangeSituation.{u}) [IsAffine D.X] [IsAffine D.S] [Epi D.hom]
    (hproj : letI : Module Γ(D.S, ⊤) Γ(D.F, ⊤) := Module.compHom Γ(D.F, ⊤) D.f.appTop.hom
      Module.Projective Γ(D.S, ⊤) Γ(D.F, ⊤)) :
    ∃ W : Over D.S, IsClosedImmersion W.hom ∧
      Nonempty (D.isomorphismFunctor.RepresentableBy W) :=
  have := projective_moduleSpecΓ_pushforward D.f D.F hproj
  D.exists_closedImmersion_representableBy_of_projective_pushforward Γ(D.S, ⊤) D.S.isoSpec

end Stacks.Flatness

end
