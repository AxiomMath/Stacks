module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.StructureSheafComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunctionPresentations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `𝐆_a` is acyclic for the direct image along an affine morphism

Let `g : Y ⟶ X` be an affine morphism of schemes. An abelian sheaf on `Y_étale` is called acyclic
here if its cohomology over `V ×_X Y` vanishes in positive degree for every affine étale
`X`-scheme `V`. Such a sheaf has an injective presentation whose direct image under `g` is still
short exact, with acyclic cokernel; so the adjunction map
`Ext^n(A, g_* M) ⟶ Ext^n(g⁻¹ A, M)` is bijective for every acyclic `M`
(`Stacks.ExtAdjunction.extMap_bijective_of_presentations`). The sheaf `𝐆_a` is acyclic, its
cohomology over an affine object vanishing in positive degree by [Stacks, Tag 03P2].

## Main definitions

* `Stacks.ArtinSchreier.IsDirectImageAcyclic`: the acyclicity condition.

## Main results

* `Stacks.ArtinSchreier.shortExact_map_directImage`: direct image carries an injective
  presentation of an acyclic sheaf to a short exact sequence.
* `Stacks.ArtinSchreier.isDirectImageAcyclic_additiveSheaf`: `𝐆_a` is acyclic.
* `Stacks.ArtinSchreier.extMap_bijective_additiveSheaf`: the adjunction map into `𝐆_a` is
  bijective.

## Implementation notes

Cohomology over an object is `Ext` out of the free abelian sheaf on the object at coefficients
`AddCommGrpCat.{u + 1}` (`Stacks.Cohomology.FreeYonedaUnivLE.freeYoneda`). The vanishing for
`𝐆_a` is proved at coefficients `AddCommGrpCat.{u}`, where [Stacks, Tag 03P2] is available, and
transported along the coefficient lift, which commutes with free sheaves
(`Stacks.ArtinSchreier.freeSheafUliftIso`) and is bijective on `Ext`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.EtaleCohomology Stacks.Cohomology.FreeYonedaUnivLE

universe w u

namespace Stacks.ArtinSchreier

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- Direct image of abelian sheaves is additive, being restriction of sections. -/
instance additive_etaleAbelianDirectImage : (etaleAbelianDirectImage.{u, 0} g).Additive :=
  ⟨fun {_ _ _ _} => rfl⟩

/-- The free abelian sheaf on an étale `Y`-scheme, at coefficients `AddCommGrpCat.{u + 1}`. -/
abbrev freeSheaf (W : Y.Etale) : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (freeYoneda.{u + 1} Y.smallEtaleTopology).obj W

variable [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **Acyclicity over the base changes of affine objects.** An abelian sheaf `M` on `Y_étale`
whose cohomology over `V ×_X Y` vanishes in positive degree for every affine étale `X`-scheme
`V`. -/
def IsDirectImageAcyclic (M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  ∀ V : X.Etale, IsAffine V.left → ∀ n : ℕ,
    Subsingleton (Ext.{w} (freeSheaf ((smallEtaleBaseChange g).obj V)) M (n + 1))

/-- A section over `W` of the quotient of a short exact sequence lifts to the middle term as soon
as the first cohomology of the subobject over `W` vanishes. -/
theorem exists_lift_of_subsingleton_ext {S : ShortComplex (Sheaf Y.smallEtaleTopology
    AddCommGrpCat.{u + 1})} (hS : S.ShortExact) (W : Y.Etale)
    (h : Subsingleton (Ext.{w} (freeSheaf W) S.X₁ 1)) (s : ToType (S.X₃.obj.obj (op W))) :
    ∃ t : ToType (S.X₂.obj.obj (op W)), S.g.hom.app (op W) t = s := by
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ (freeSheaf W) hS
    (Ext.mk₀ ((sectionsAddEquiv.{u + 1} W S.X₃).symm s)) (zero_add 1) (by subsingleton)
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₂
  rw [Ext.mk₀_comp_mk₀] at hx₂
  refine ⟨sectionsEquiv.{u + 1} W S.X₂ φ, ?_⟩
  rw [← sectionsEquiv_naturality, (Ext.mk₀_bijective _ _).1 hx₂]
  exact (sectionsAddEquiv.{u + 1} W S.X₃).apply_symm_apply s

/-- **Direct image carries an injective presentation of an acyclic sheaf to a short exact
sequence.** -/
theorem shortExact_map_directImage {S : ShortComplex (Sheaf Y.smallEtaleTopology
    AddCommGrpCat.{u + 1})} (hS : S.ShortExact) (hM : IsDirectImageAcyclic.{w} g S.X₁) :
    (S.map (etaleAbelianDirectImage.{u, 0} g)).ShortExact := by
  have hlim := (etaleAbelianInverseImageDirectImageAdj.{u, 0} g).rightAdjoint_preservesLimits.{0, 0}
  have hker : PreservesLimit (parallelPair S.g 0) (etaleAbelianDirectImage.{u, 0} g) :=
    hlim.preservesLimitsOfShape.preservesLimit
  have hexact : (S.map (etaleAbelianDirectImage.{u, 0} g)).Exact :=
    hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f hker
  have hpm : (etaleAbelianDirectImage.{u, 0} g).PreservesMonomorphisms :=
    @preservesMonomorphisms_of_preservesLimitsOfShape _ _ _ _ _
      hlim.preservesLimitsOfShape
  have := hS.mono_f
  have hmf : Mono (S.map (etaleAbelianDirectImage.{u, 0} g)).f :=
    (etaleAbelianDirectImage.{u, 0} g).map_mono S.f
  refine ShortComplex.ShortExact.mk' hexact hmf ?_
  have : Sheaf.IsLocallySurjective ((etaleAbelianDirectImage.{u, 0} g).map S.g) := by
    refine ⟨fun {U} s => ?_⟩
    refine X.smallEtaleTopology.superset_covering ?_
      ((Scheme.AffineEtale.Spec X).is_cover_of_isCoverDense X.smallEtaleTopology U)
    rintro V f ⟨⟨R, f₁, f₂, rfl⟩⟩
    refine Sieve.downward_closed _ ?_ f₁
    have hR : IsAffine ((Scheme.AffineEtale.Spec X).obj R).left :=
      inferInstanceAs (IsAffine (Spec _))
    exact exists_lift_of_subsingleton_ext.{w} hS
      ((smallEtaleBaseChange g).obj ((Scheme.AffineEtale.Spec X).obj R)) (hM _ hR 0)
      (((etaleAbelianDirectImage.{u, 0} g).obj S.X₃).obj.map f₂.op s)
  exact Sheaf.epi_of_isLocallySurjective ((etaleAbelianDirectImage.{u, 0} g).map S.g)

attribute [local instance] Ext.subsingleton_of_injective in
/-- **The cokernel of an injective presentation of an acyclic sheaf is acyclic.** -/
theorem isDirectImageAcyclic_X₃ {S : ShortComplex (Sheaf Y.smallEtaleTopology
    AddCommGrpCat.{u + 1})} (hS : S.ShortExact) [Injective S.X₂]
    (hM : IsDirectImageAcyclic.{w} g S.X₁) : IsDirectImageAcyclic.{w} g S.X₃ := by
  intro V hV n
  refine ⟨fun a b => ?_⟩
  have key : ∀ x : Ext.{w} (freeSheaf ((smallEtaleBaseChange g).obj V)) S.X₃ (n + 1), x = 0 := by
    intro x
    have := hM V hV (n + 1)
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hS x rfl (by subsingleton)
    rw [← hx₂, Subsingleton.elim x₂ 0, Ext.zero_comp]
  rw [key a, key b]

section Ulift

omit [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- A commutative square of maps of types induces a commutative square of free abelian
groups. -/
theorem freeAbelianGroup_map_comm {α β γ δ : Type*} (f : α → β) (e₁ : α → γ) (e₂ : β → δ)
    (f' : γ → δ) (h : ∀ a, e₂ (f a) = f' (e₁ a)) (x : FreeAbelianGroup α) :
    FreeAbelianGroup.map e₂ (FreeAbelianGroup.map f x) =
      FreeAbelianGroup.map f' (FreeAbelianGroup.map e₁ x) := by
  rw [← FreeAbelianGroup.map_comp_apply, ← FreeAbelianGroup.map_comp_apply]
  exact congrArg (fun φ => FreeAbelianGroup.map φ x) (funext h)

/-- The free abelian presheaf on a representable presheaf, with its coefficients raised, is the
free abelian presheaf at the larger coefficient universe. -/
def freePresheafUliftIso (W : Y.Etale) :
    (uliftYoneda.{u}.obj W ⋙ AddCommGrpCat.free) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free :=
  NatIso.ofComponents (fun V =>
      (show ULift.{u + 1} (FreeAbelianGroup ((uliftYoneda.{u}.obj W).obj V)) ≃+
          FreeAbelianGroup ((uliftYoneda.{u + 1}.obj W).obj V) from
        AddEquiv.ulift.trans (FreeAbelianGroup.equivOfEquiv
          { toFun := fun x => ⟨x.down⟩, invFun := fun x => ⟨x.down⟩,
            left_inv := fun _ => rfl, right_inv := fun _ => rfl })).toAddCommGrpIso)
    (fun {V V'} h => by
      apply AddCommGrpCat.hom_ext
      ext ⟨x⟩
      exact freeAbelianGroup_map_comm ((uliftYoneda.{u}.obj W).map h)
        (fun t => (⟨t.down⟩ : (uliftYoneda.{u + 1}.obj W).obj V))
        (fun t => (⟨t.down⟩ : (uliftYoneda.{u + 1}.obj W).obj V'))
        ((uliftYoneda.{u + 1}.obj W).map h) (fun _ => rfl) x)

omit [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- The free abelian sheaf on an étale `Y`-scheme, with its coefficients raised from
`AddCommGrpCat.{u}` to `AddCommGrpCat.{u + 1}`, is the free abelian sheaf at the larger
coefficient universe. -/
def freeSheafUliftIso (W : Y.Etale) :
    (sheafCompose Y.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        ((freeYoneda.{u} Y.smallEtaleTopology).obj W) ≅ freeSheaf W :=
  haveI := (etaleUlift_properties.{u, u, u + 1} Y).1
  ((sheafComposeNatIso Y.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
      (sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u})
      (sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u + 1})).app
        (uliftYoneda.{u}.obj W ⋙ AddCommGrpCat.free)).symm ≪≫
    (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso (freePresheafUliftIso W)

end Ulift

attribute [local instance 3000] AlgebraicGeometry.enoughInjectives_sheaf_smallEtaleTopology
  AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology in
attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt in
/-- **`𝐆_a` is acyclic over the base change of an affine object along an affine morphism.** For
`g : Y ⟶ X` affine and `V` an affine étale `X`-scheme, the cohomology of `𝐆_{a,Y}` over the
affine étale `Y`-scheme `V ×_X Y` vanishes in positive degree. -/
@[sga "4 VII 4.4" "special case"]
theorem isDirectImageAcyclic_additiveSheaf [IsAffineHom g] :
    IsDirectImageAcyclic.{w} g (additiveSheaf.{u, u + 1} Y) := by
  intro V hV n
  let W := (smallEtaleBaseChange g).obj V
  have hW : IsAffine W.left := by
    have h : IsAffineHom (pullback.fst V.hom g) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback V.hom g).flip
        ‹IsAffineHom g›
    exact @isAffine_of_isAffineHom _ _ (pullback.fst V.hom g) h hV
  have := (etaleUlift_properties.{u, u, u + 1} Y).1
  have := (etaleUlift_properties.{u, u, u + 1} Y).2
  let L := sheafCompose Y.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
  have : L.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits L :=
    Stacks.Cohomology.CoefficientLift.uliftSheafCompose_preservesFiniteLimits.{u, u + 1}
      Y.smallEtaleTopology
  have : PreservesFiniteColimits L :=
    Stacks.Cohomology.CoefficientLift.uliftSheafCompose_preservesFiniteColimits.{u, u + 1}
      Y.smallEtaleTopology
  have h0 : Subsingleton (Ext.{u} ((freeYoneda.{u} Y.smallEtaleTopology).obj W)
      (smallEtaleAssociatedSheaf Y (Scheme.unitModule Y)) (n + 1)) := by
    have hz := isZero_sheafCohomology_succ_smallEtaleAffine Y (Scheme.unitModule Y) W hW (n + 1)
      (Nat.succ_pos n)
    exact AddCommGrpCat.subsingleton_of_isZero (hz.of_iso
      (cohomologyPresheafObjIsoPinned.{u} Y.smallEtaleTopology _ (n + 1) W))
  have h1 : Subsingleton (Ext.{u} ((freeYoneda.{u} Y.smallEtaleTopology).obj W)
      (additiveSheafBase Y) (n + 1)) :=
    (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
      (additiveSheafBaseIsoSmallEtaleAssociatedSheaf Y).hom (n + 1)).injective.subsingleton
  have h2 : Subsingleton (Ext.{w} (L.obj ((freeYoneda.{u} Y.smallEtaleTopology).obj W))
      (L.obj (additiveSheafBase Y)) (n + 1)) :=
    (L.mapExt_bijective_of_preservesInjectiveObjects _ _ (n + 1)).surjective.subsingleton
  have h3 : Subsingleton (Ext.{w} (freeSheaf W) (L.obj (additiveSheafBase Y)) (n + 1)) :=
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso
      (freeSheafUliftIso W).hom (n + 1)).injective.subsingleton
  exact (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
    (additiveSheafBaseUliftIso Y).inv (n + 1)).injective.subsingleton

/-- **The adjunction map into `𝐆_{a,Y}` is bijective** for an affine morphism `g : Y ⟶ X`:
`Ext^n(A, g_* 𝐆_{a,Y}) ⟶ Ext^n(g⁻¹ A, 𝐆_{a,Y})` is bijective for every abelian sheaf `A` on
`X_étale` and every `n`. -/
theorem extMap_bijective_additiveSheaf [IsAffineHom g]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Function.Bijective (Stacks.ExtAdjunction.extMap
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} g) A (additiveSheaf.{u, u + 1} Y) n :
        Ext.{w} A _ n → Ext.{w} _ _ n) := by
  have : IsGrothendieckAbelian.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse Y
  refine Stacks.ExtAdjunction.extMap_bijective_of_presentations _
    (IsDirectImageAcyclic.{w} g) (fun M hM => ?_) A n _ (isDirectImageAcyclic_additiveSheaf g)
  let I : InjectivePresentation M := Classical.arbitrary _
  let S := ShortComplex.mk _ _ (cokernel.condition I.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
  have : Injective S.X₂ := I.injective
  exact ⟨S, hS, shortExact_map_directImage g hS hM, I.injective,
    isDirectImageAcyclic_X₃ g hS hM, rfl⟩

end Stacks.ArtinSchreier

end
