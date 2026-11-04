module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentEdsPieces
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectFullyFaithfulHeld

/-!
# The square step of the essential surjectivity in Stacks 0DKW

In Situation 0DKU let `(U₀ ⊆ X₀, V₀ ⟶ X₀)` be an elementary distinguished square of `X₀` whose
three pieces are of finite presentation over `X₀`.  The source's proof of Stacks 0DKW shows that
if every `Y`-perfect object over the limit of the situations over `U₀` and over `V₀` comes from a
stage, and the comparison out of the colimit is fully faithful for the situation over
`P₀ = U₀ ×_{X₀} V₀`, then every `Y`-perfect object of `D(𝒪_X)` comes from a stage: the two
objects at a common stage are compared over `P₀` by an isomorphism descended from the limit by
full faithfulness, glued by the first assertion of Stacks 08HB, and the glued object pulls back
to the given one by its second assertion
(`AlgebraicGeometry.Space.exists_glue_derivedPullback_iso_of_edsPreimage`).  The glued object is
`Yᵢ`-perfect because relative perfectness is étale local (a consequence of Stacks 0DKQ).

## Main definitions

* `AlgebraicGeometry.Space.EtaleLocalRelativelyPerfect`: the two consequences of Stacks 0DKQ
  used here, carried as a hypothesis and proved by
  `AlgebraicGeometry.Space.etaleLocalRelativelyPerfect`.

## Main results

* `AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso_prism`: the identifications of
  the faces of a commutative prism of derived pullbacks paste coherently.
* `AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectEssentiallySurjective_of_eds`:
  the square step.

## References

* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Tag 0DKQ](https://stacks.math.columbia.edu/tag/0DKQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace DerivedPullbackComposition

variable (P : DerivedPullbackComposition B S hS)

/-- The map on derived homomorphisms induced by a factorisation is compatible with
composition of morphisms. -/
theorem factorHom_morphism_comp {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k)
    (K L M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (χ : (smallEtaleDerivedModulePullback B S hS g).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj L)
    (χ' : (smallEtaleDerivedModulePullback B S hS g).obj L ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj M) :
    P.factorHom f g k h K M (χ ≫ χ') = P.factorHom f g k h K L χ ≫ P.factorHom f g k h L M χ' := by
  simp [factorHom, Iso.homCongr_apply]

/-- The map on derived homomorphisms induced by a factorisation carries identities to
identities. -/
theorem factorHom_morphism_id {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    P.factorHom f g k h K K (𝟙 _) = 𝟙 _ := by
  simp [factorHom, Iso.homCongr_apply]

/-- **The identifications of the faces of a commutative prism paste coherently.**  For a
commutative prism of algebraic spaces

```
P' --pP--> Pn --tP--> Pk
|fst'      |fstn      |fstk
v          v          v
U' --pU--> Un --tU--> Uk
```

with `pP ≫ tP = pPk` and `pU ≫ tU = pUk`, the two composites of face identifications from
`LpP^*(Lfstn^*(LtU^*A))` to `Lfst'^*(LpUk^*A)` agree. -/
theorem squareIso_prism {P' Pn Pk U' Un Uk : AlgebraicSpaces B S hS}
    (fst' : P' ⟶ U') (fstn : Pn ⟶ Un) (fstk : Pk ⟶ Uk) (pP : P' ⟶ Pn) (tP : Pn ⟶ Pk)
    (pPk : P' ⟶ Pk) (pU : U' ⟶ Un) (tU : Un ⟶ Uk) (pUk : U' ⟶ Uk)
    (hn : fst' ≫ pU = pP ≫ fstn) (ht : fstn ≫ tU = tP ≫ fstk) (hk : fst' ≫ pUk = pPk ≫ fstk)
    (hP : pP ≫ tP = pPk) (hU : pU ≫ tU = pUk)
    (A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Uk))) :
    (smallEtaleDerivedModulePullback B S hS pP).map
        ((P.squareIso fstn tU tP fstk ht).inv.app A) ≫
      (P.iso pP tP pPk hP).hom.app ((smallEtaleDerivedModulePullback B S hS fstk).obj A) ≫
      (P.squareIso fst' pUk pPk fstk hk).hom.app A =
    (P.squareIso fst' pU pP fstn hn).hom.app ((smallEtaleDerivedModulePullback B S hS tU).obj A) ≫
      (smallEtaleDerivedModulePullback B S hS fst').map ((P.iso pU tU pUk hU).hom.app A) := by
  -- the diagonal of the prism
  let T := fst' ≫ pUk
  have hT₁ : pPk ≫ fstk = T := hk.symm
  have hT₂ : pP ≫ (fstn ≫ tU) = T := by
    rw [ht, ← Category.assoc, hP, hT₁]
  have hT₃ : (fst' ≫ pU) ≫ tU = T := by
    rw [Category.assoc, hU]
  let Xiso := (P.iso fst' pUk T rfl).app A
  refine (Iso.cancel_iso_hom_right _ _ Xiso).1 ?_
  -- the left side
  have hL : (P.squareIso fst' pUk pPk fstk hk).hom.app A ≫ Xiso.hom =
      (P.iso pPk fstk T hT₁).hom.app A := by
    simp [squareIso, Xiso, T]
  have hL₂ : (P.iso pP tP pPk hP).hom.app ((smallEtaleDerivedModulePullback B S hS fstk).obj A) ≫
      (P.iso pPk fstk T hT₁).hom.app A =
      (smallEtaleDerivedModulePullback B S hS pP).map
          ((P.iso tP fstk (fstn ≫ tU) ht.symm).hom.app A) ≫
        (P.iso pP (fstn ≫ tU) T hT₂).hom.app A :=
    P.iso_hom_app_comp_iso_hom_app pP tP fstk (fstn ≫ tU) pPk T ht.symm hP hT₁ hT₂ A
  have hL₃ : (smallEtaleDerivedModulePullback B S hS pP).map
        ((P.squareIso fstn tU tP fstk ht).inv.app A) ≫
      (smallEtaleDerivedModulePullback B S hS pP).map
          ((P.iso tP fstk (fstn ≫ tU) ht.symm).hom.app A) =
      (smallEtaleDerivedModulePullback B S hS pP).map
          ((P.iso fstn tU (fstn ≫ tU) rfl).hom.app A) := by
    rw [← Functor.map_comp]
    congr 1
    simp [squareIso]
  have hL₄ : (smallEtaleDerivedModulePullback B S hS pP).map
        ((P.iso fstn tU (fstn ≫ tU) rfl).hom.app A) ≫ (P.iso pP (fstn ≫ tU) T hT₂).hom.app A =
      (P.iso pP fstn (fst' ≫ pU) hn.symm).hom.app
          ((smallEtaleDerivedModulePullback B S hS tU).obj A) ≫
        (P.iso (fst' ≫ pU) tU T hT₃).hom.app A :=
    (P.iso_hom_app_comp_iso_hom_app pP fstn tU (fstn ≫ tU) (fst' ≫ pU) T rfl hn.symm hT₃ hT₂
      A).symm
  -- the right side
  have hR : (smallEtaleDerivedModulePullback B S hS fst').map ((P.iso pU tU pUk hU).hom.app A) ≫
      Xiso.hom = (P.iso fst' pU (fst' ≫ pU) rfl).hom.app
          ((smallEtaleDerivedModulePullback B S hS tU).obj A) ≫
        (P.iso (fst' ≫ pU) tU T hT₃).hom.app A :=
    (P.iso_hom_app_comp_iso_hom_app fst' pU tU pUk (fst' ≫ pU) T hU rfl hT₃ rfl A).symm
  have hR₂ : (P.squareIso fst' pU pP fstn hn).hom.app
        ((smallEtaleDerivedModulePullback B S hS tU).obj A) ≫
      (P.iso fst' pU (fst' ≫ pU) rfl).hom.app ((smallEtaleDerivedModulePullback B S hS tU).obj A) =
      (P.iso pP fstn (fst' ≫ pU) hn.symm).hom.app
        ((smallEtaleDerivedModulePullback B S hS tU).obj A) := by
    simp [squareIso]
  simp only [Category.assoc]
  rw [hL, hL₂, ← Category.assoc, hL₃, hL₄, hR, ← Category.assoc, hR₂]

/-- `AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso_prism`, read on inverses. -/
theorem squareIso_prism_inv {P' Pn Pk U' Un Uk : AlgebraicSpaces B S hS}
    (fst' : P' ⟶ U') (fstn : Pn ⟶ Un) (fstk : Pk ⟶ Uk) (pP : P' ⟶ Pn) (tP : Pn ⟶ Pk)
    (pPk : P' ⟶ Pk) (pU : U' ⟶ Un) (tU : Un ⟶ Uk) (pUk : U' ⟶ Uk)
    (hn : fst' ≫ pU = pP ≫ fstn) (ht : fstn ≫ tU = tP ≫ fstk) (hk : fst' ≫ pUk = pPk ≫ fstk)
    (hP : pP ≫ tP = pPk) (hU : pU ≫ tU = pUk)
    (A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Uk))) :
    (P.squareIso fst' pUk pPk fstk hk).inv.app A ≫
      (P.iso pP tP pPk hP).inv.app ((smallEtaleDerivedModulePullback B S hS fstk).obj A) ≫
      (smallEtaleDerivedModulePullback B S hS pP).map
        ((P.squareIso fstn tU tP fstk ht).hom.app A) =
    (smallEtaleDerivedModulePullback B S hS fst').map ((P.iso pU tU pUk hU).inv.app A) ≫
      (P.squareIso fst' pU pP fstn hn).inv.app
        ((smallEtaleDerivedModulePullback B S hS tU).obj A) := by
  let X := (smallEtaleDerivedModulePullback B S hS pP).mapIso
      ((P.squareIso fstn tU tP fstk ht).app A).symm ≪≫
    (P.iso pP tP pPk hP).app ((smallEtaleDerivedModulePullback B S hS fstk).obj A) ≪≫
    (P.squareIso fst' pUk pPk fstk hk).app A
  have h : X.hom = ((P.squareIso fst' pU pP fstn hn).app
      ((smallEtaleDerivedModulePullback B S hS tU).obj A) ≪≫
      (smallEtaleDerivedModulePullback B S hS fst').mapIso ((P.iso pU tU pUk hU).app A)).hom :=
    P.squareIso_prism fst' fstn fstk pP tP pPk pU tU pUk hn ht hk hP hU A
  have h' := congrArg Iso.inv (Iso.ext h)
  simpa [X, ← Functor.map_comp] using h'

/-- The map on derived homomorphisms induced by a factorisation `f ≫ g = k` only depends on the
image of the morphism under `Lf^*`. -/
theorem factorHom_congr_map {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k)
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))}
    {χ χ' : (smallEtaleDerivedModulePullback B S hS g).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj L}
    (hχ : (smallEtaleDerivedModulePullback B S hS f).map χ =
      (smallEtaleDerivedModulePullback B S hS f).map χ') :
    P.factorHom f g k h K L χ = P.factorHom f g k h K L χ' := by
  simp only [factorHom, hχ]

/-- The map on derived homomorphisms induced by a factorisation detects equality of the images
under `Lf^*`. -/
theorem map_eq_of_factorHom_eq {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (h : f ≫ g = k)
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))}
    {χ χ' : (smallEtaleDerivedModulePullback B S hS g).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj L}
    (hχ : P.factorHom f g k h K L χ = P.factorHom f g k h K L χ') :
    (smallEtaleDerivedModulePullback B S hS f).map χ =
      (smallEtaleDerivedModulePullback B S hS f).map χ' :=
  ((P.iso f g k h).app K).homCongr ((P.iso f g k h).app L) |>.injective hχ

/-- A composite of morphisms has the same image under `Lf^*` as the identity if and only if the
induced maps on derived homomorphisms compose to the identity. -/
private theorem map_comp_eq_map_id_iff {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (h : f ≫ g = k)
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))}
    (a : (smallEtaleDerivedModulePullback B S hS g).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj L)
    (b : (smallEtaleDerivedModulePullback B S hS g).obj L ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj K) :
    (smallEtaleDerivedModulePullback B S hS f).map (a ≫ b) =
        (smallEtaleDerivedModulePullback B S hS f).map (𝟙 _) ↔
      P.factorHom f g k h K L a ≫ P.factorHom f g k h L K b = 𝟙 _ := by
  rw [← P.factorHom_morphism_comp f g k h K L K a b, ← P.factorHom_morphism_id f g k h K]
  exact ⟨P.factorHom_congr_map f g k h, P.map_eq_of_factorHom_eq f g k h⟩

end DerivedPullbackComposition

/-! ### Relative perfectness is étale local -/

variable (B S hS) in
/-- **The two consequences of Stacks 0DKQ used in the square step.**  Relative perfectness
(Stacks 0DKN) is étale local on the source:
1. for `f : X ⟶ Y` flat and locally of finite presentation and an étale `a : X' ⟶ X`, the
   derived pullback `La^*K` of a `Y`-perfect `K` is `Y`-perfect along `a ≫ f`;
2. for an elementary distinguished square `(U ⊆ W, V ⟶ W)` and `f : W ⟶ Y` flat and locally of
   finite presentation, an object of `D(𝒪_W)` whose restrictions to `U` and to `V` are
   `Y`-perfect is `Y`-perfect.

This proposition is proved by `AlgebraicGeometry.Space.etaleLocalRelativelyPerfect`.  For a
general étale square the library states the same two facts as
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_smallEtaleDerivedModulePullback_of_isEtale`
(of which (1) is the case where the étale map of the base is the identity) and
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_forall_isEtale` (of which (2) is the
case of the two pieces of an elementary distinguished square, which cover `|W|`), on the way to
Stacks 0DKQ. -/
def EtaleLocalRelativelyPerfect : Prop :=
  (∀ {X X' Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (a : X' ⟶ X)
      (hfl : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
      (hfl' : IsFlat B S hS (a ≫ f).hom)
      (hlfp' : IsLocallyOfFinitePresentation B S hS (a ≫ f).hom),
      IsEtale B S hS a.hom → ∀ K : derivedModules B S hS X,
        RelativeDescentSituation.IsPerfectAlong f hfl hlfp K →
          RelativeDescentSituation.IsPerfectAlong (a ≫ f) hfl' hlfp'
            ((smallEtaleDerivedModulePullback B S hS a).obj K)) ∧
    ∀ {W Y : AlgebraicSpaces B S hS} (f : W ⟶ Y) (hfl : IsFlat B S hS f.hom)
      (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) {Uo : Subfunctor W.1}
      {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {fV : V ⟶ W.1}
      (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
      (hflU : IsFlat B S hS (edsOpenHom B S hS hsq ≫ f).hom)
      (hlfpU : IsLocallyOfFinitePresentation B S hS (edsOpenHom B S hS hsq ≫ f).hom)
      (hflV : IsFlat B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
      (hlfpV : IsLocallyOfFinitePresentation B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
      (K : derivedModules B S hS W),
      RelativeDescentSituation.IsPerfectAlong (edsOpenHom B S hS hsq ≫ f) hflU hlfpU
          ((smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq)).obj K) →
        RelativeDescentSituation.IsPerfectAlong (edsEtaleHom B S hS hsq ≫ f) hflV hlfpV
          ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj K) →
        RelativeDescentSituation.IsPerfectAlong f hfl hlfp K

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

section GlueTwoStages

attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

local notation "𝐋 " f => smallEtaleDerivedModulePullback _ _ _ f
local notation "𝐏" => DerivedPullbackComposition.canonical _ _ _

/-- **Glueing at a later stage along an overlap isomorphism descended from the limit.**  Let
`(Uₙ ⊆ Wₙ, Vₙ ⟶ Wₙ)` and `(U' ⊆ W', V' ⟶ W')` be elementary distinguished squares with a
morphism `p : W' ⟶ Wₙ` between them (a commutative cube with faces `pU`, `pV`, `pP`), and let
`tU : Uₙ ⟶ Uₖ`, `tV : Vₙ ⟶ Vₖ`, `tP : Pₙ ⟶ Pₖ` map the pieces to the pieces `Uₖ`, `Vₖ`, `Pₖ` of
an earlier stage, compatibly with the projections `fstₖ`, `sndₖ` of `Pₖ` and with `pU`, `pV`,
`pP`.  Let `E ∈ D(𝒪_{W'})`, `A ∈ D(𝒪_{Uₖ})` and `Bo ∈ D(𝒪_{Vₖ})` with `αU : A|_{U'} ≅ E|_{U'}`
and `αV : Bo|_{V'} ≅ E|_{V'}`, and let `ψ : (A|_{Pₖ})|_{Pₙ} ≅ (Bo|_{Pₖ})|_{Pₙ}` induce over `P'`
the identification of `A|_{P'}` with `Bo|_{P'}` given by `αU` and `αV`.  Then `A|_{Uₙ}` and
`Bo|_{Vₙ}` glue to an object `F` of `D(𝒪_{Wₙ})` with `Lp^*F ≅ E`. -/
theorem exists_glue_of_descended_iso
    {Wn W' : AlgebraicSpaces B S hS} {V V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor Wn.1} {Uo' : Subfunctor W'.1} {fV : V ⟶ Wn.1} {fV' : V' ⟶ W'.1}
    (hsq : IsElementaryDistinguishedSquare B S hS Wn.2 Uo fV)
    (hsq' : IsElementaryDistinguishedSquare B S hS W'.2 Uo' fV')
    (p : W' ⟶ Wn) (pU : edsOpen B S hS hsq' ⟶ edsOpen B S hS hsq)
    (pV : edsEtale B S hS hsq' ⟶ edsEtale B S hS hsq)
    (pP : edsInter B S hS hsq' ⟶ edsInter B S hS hsq)
    (hU : edsOpenHom B S hS hsq' ≫ p = pU ≫ edsOpenHom B S hS hsq)
    (hV : edsEtaleHom B S hS hsq' ≫ p = pV ≫ edsEtaleHom B S hS hsq)
    (hPU : edsFst B S hS hsq' ≫ pU = pP ≫ edsFst B S hS hsq)
    (hPV : edsSnd B S hS hsq' ≫ pV = pP ≫ edsSnd B S hS hsq)
    {Uk Vk Pk : AlgebraicSpaces B S hS} (fstk : Pk ⟶ Uk) (sndk : Pk ⟶ Vk)
    (tU : edsOpen B S hS hsq ⟶ Uk) (tV : edsEtale B S hS hsq ⟶ Vk)
    (tP : edsInter B S hS hsq ⟶ Pk)
    (htU : edsFst B S hS hsq ≫ tU = tP ≫ fstk) (htV : edsSnd B S hS hsq ≫ tV = tP ≫ sndk)
    (pUk : edsOpen B S hS hsq' ⟶ Uk) (pVk : edsEtale B S hS hsq' ⟶ Vk)
    (pPk : edsInter B S hS hsq' ⟶ Pk)
    (hPUk : edsFst B S hS hsq' ≫ pUk = pPk ≫ fstk) (hPVk : edsSnd B S hS hsq' ≫ pVk = pPk ≫ sndk)
    (hUU : pU ≫ tU = pUk) (hVV : pV ≫ tV = pVk) (hPP : pP ≫ tP = pPk)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W')))
    (A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Uk)))
    (Bo : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Vk)))
    (αU : (𝐋 pUk).obj A ≅ (𝐋 (edsOpenHom B S hS hsq')).obj E)
    (αV : (𝐋 pVk).obj Bo ≅ (𝐋 (edsEtaleHom B S hS hsq')).obj E)
    (ψ : (𝐋 tP).obj ((𝐋 fstk).obj A) ≅ (𝐋 tP).obj ((𝐋 sndk).obj Bo))
    (hψ : (𝐏).factorHom pP tP pPk hPP ((𝐋 fstk).obj A) ((𝐋 sndk).obj Bo) ψ.hom =
      (((𝐏).squareIso (edsFst B S hS hsq') pUk pPk fstk hPUk).app A ≪≫
        (𝐋 (edsFst B S hS hsq')).mapIso αU ≪≫
        ((𝐏).squareIso (edsSnd B S hS hsq') (edsEtaleHom B S hS hsq') (edsFst B S hS hsq')
          (edsOpenHom B S hS hsq') (isPullback_edsInter B S hS hsq').flip.w).app E ≪≫
        (𝐋 (edsSnd B S hS hsq')).mapIso αV.symm ≪≫
        (((𝐏).squareIso (edsSnd B S hS hsq') pVk pPk sndk hPVk).app Bo).symm).hom) :
    ∃ (F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Wn)))
      (_ : (𝐋 (edsOpenHom B S hS hsq)).obj F ≅ (𝐋 tU).obj A)
      (_ : (𝐋 (edsEtaleHom B S hS hsq)).obj F ≅ (𝐋 tV).obj Bo),
      Nonempty ((𝐋 p).obj F ≅ E) := by
  obtain ⟨αUn, hαU⟩ : ∃ α : (𝐋 pU).obj ((𝐋 tU).obj A) ≅ (𝐋 (edsOpenHom B S hS hsq')).obj E,
      α.hom = ((𝐏).iso pU tU pUk hUU).hom.app A ≫ αU.hom :=
    ⟨((𝐏).iso pU tU pUk hUU).app A ≪≫ αU, rfl⟩
  obtain ⟨αVn, hαV⟩ : ∃ α : (𝐋 pV).obj ((𝐋 tV).obj Bo) ≅ (𝐋 (edsEtaleHom B S hS hsq')).obj E,
      α.inv = αV.inv ≫ ((𝐏).iso pV tV pVk hVV).inv.app Bo :=
    ⟨((𝐏).iso pV tV pVk hVV).app Bo ≪≫ αV, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : (𝐋 (edsFst B S hS hsq)).obj ((𝐋 tU).obj A) ≅
      (𝐋 (edsSnd B S hS hsq)).obj ((𝐋 tV).obj Bo),
      c.hom = ((𝐏).squareIso (edsFst B S hS hsq) tU tP fstk htU).inv.app A ≫ ψ.hom ≫
        ((𝐏).squareIso (edsSnd B S hS hsq) tV tP sndk htV).hom.app Bo :=
    ⟨(((𝐏).squareIso (edsFst B S hS hsq) tU tP fstk htU).app A).symm ≪≫ ψ ≪≫
      ((𝐏).squareIso (edsSnd B S hS hsq) tV tP sndk htV).app Bo, rfl⟩
  have hψ' : (𝐋 pP).map ψ.hom =
      ((𝐏).iso pP tP pPk hPP).hom.app ((𝐋 fstk).obj A) ≫
        ((𝐏).squareIso (edsFst B S hS hsq') pUk pPk fstk hPUk).hom.app A ≫
        (𝐋 (edsFst B S hS hsq')).map αU.hom ≫
        ((𝐏).squareIso (edsSnd B S hS hsq') (edsEtaleHom B S hS hsq') (edsFst B S hS hsq')
          (edsOpenHom B S hS hsq') (isPullback_edsInter B S hS hsq').flip.w).hom.app E ≫
        (𝐋 (edsSnd B S hS hsq')).map αV.inv ≫
        ((𝐏).squareIso (edsSnd B S hS hsq') pVk pPk sndk hPVk).inv.app Bo ≫
        ((𝐏).iso pP tP pPk hPP).inv.app ((𝐋 sndk).obj Bo) := by
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv] at hψ
    have h₁ := (Iso.inv_comp_eq (((𝐏).iso pP tP pPk hPP).app ((𝐋 fstk).obj A))).1 hψ
    have h₂ := (Iso.eq_comp_inv (((𝐏).iso pP tP pPk hPP).app ((𝐋 sndk).obj Bo))).2 h₁
    simpa only [Category.assoc, Iso.app_hom, Iso.app_inv] using h₂
  refine exists_glue_derivedPullback_iso_of_eds hsq hsq' p pU pV pP hU hV hPU hPV E _ _ αUn αVn c
    ?_
  have eU := (𝐏).squareIso_prism (edsFst B S hS hsq') (edsFst B S hS hsq) fstk pP tP pPk pU tU
    pUk hPU htU hPUk hPP hUU A
  have eV := (𝐏).squareIso_prism_inv (edsSnd B S hS hsq') (edsSnd B S hS hsq) sndk pP tP pPk pV
    tV pVk hPV htV hPVk hPP hVV Bo
  simp only [hc, Functor.map_comp, hψ', hαU, hαV, Category.assoc]
  simp only [reassoc_of% eU, eV]

end GlueTwoStages

namespace RelativeDescentSituation

/-- Relative perfectness is invariant under isomorphism (Stacks 0DKR). -/
theorem isPerfectAlong_of_iso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfl : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    {K K' : derivedModules B S hS X} (e : K ≅ K') (hK : IsPerfectAlong f hfl hlfp K) :
    IsPerfectAlong f hfl hlfp K' :=
  have := isClosedUnderIsomorphisms_isPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl
    hlfp
  (isPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp).prop_of_iso e hK

/-- Relative perfectness along equal morphisms agrees. -/
theorem isPerfectAlong_congr {X Y : AlgebraicSpaces B S hS} {f f' : X ⟶ Y} (h : f = f')
    (hfl : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (hfl' : IsFlat B S hS f'.hom) (hlfp' : IsLocallyOfFinitePresentation B S hS f'.hom)
    {K : derivedModules B S hS X} (hK : IsPerfectAlong f hfl hlfp K) :
    IsPerfectAlong f' hfl' hlfp' K := by
  subst h
  exact hK

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

/-- **Fullness, read with the canonical pseudofunctoriality datum.**  In a situation whose
comparison out of the colimit is full, every morphism `Lfₖ^*K ⟶ Lfₖ^*M` between derived pullbacks
of `Yₖ`-perfect objects is induced, through the canonical identification
`L(f_{mk})^* ⋙ L(f_m)^* ≅ L(f_k)^*`, by a morphism at some stage `m ≥ k`. -/
theorem exists_factorHom_eq_of_fullyFaithful (hff : D.RelativelyPerfectFullyFaithful)
    (hD : D.IsSchemeLimit) {k : D.LaterIndex} (K M : derivedModules B S hS (D.stageSource k))
    (hK : D.IsStagePerfect k K) (hM : D.IsStagePerfect k M)
    (χ : (smallEtaleDerivedModulePullback B S hS (D.sourceProjection k)).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS (D.sourceProjection k)).obj M) :
    ∃ (m : D.LaterIndex) (hkm : k.1 ≤ m.1)
      (ψ : (smallEtaleDerivedModulePullback B S hS (D.sourceTransition hkm)).obj K ⟶
        (smallEtaleDerivedModulePullback B S hS (D.sourceTransition hkm)).obj M),
      (DerivedPullbackComposition.canonical B S hS).factorHom (D.sourceProjection m)
        (D.sourceTransition hkm) (D.sourceProjection k)
        (D.sourceProjection_comp_sourceTransition hkm) K M ψ = χ := by
  obtain ⟨m, hkm, ψ, hψ⟩ := (hff hD).1 k K M hK hM χ
  refine ⟨m, hkm, ψ, ?_⟩
  rw [hψ]
  exact (DerivedPullbackComposition.canonical B S hS).factorHom_eq_conjHom _ _ _ _
    (DerivedPullbackComposition.canonical_iso_eq_triangle_symm _ _ _ _) K M ψ

/-- Transporting a morphism at a stage `m ≥ k` to a later stage `n ≥ m` along the canonical
identifications does not change the morphism it induces at the limit. -/
theorem factorHom_transport {k m n : D.LaterIndex} (hkm : k.1 ≤ m.1) (hmn : m.1 ≤ n.1)
    (K M : derivedModules B S hS (D.stageSource k))
    (ψ : (smallEtaleDerivedModulePullback B S hS (D.sourceTransition hkm)).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS (D.sourceTransition hkm)).obj M) :
    (DerivedPullbackComposition.canonical B S hS).factorHom (D.sourceProjection n)
        (D.sourceTransition (hkm.trans hmn)) (D.sourceProjection k)
        (D.sourceProjection_comp_sourceTransition (hkm.trans hmn)) K M
        ((DerivedPullbackComposition.canonical B S hS).factorHom (D.sourceTransition hmn)
          (D.sourceTransition hkm) (D.sourceTransition (hkm.trans hmn))
          (D.sourceTransition_comp_sourceTransition hkm hmn) K M ψ) =
      (DerivedPullbackComposition.canonical B S hS).factorHom (D.sourceProjection m)
        (D.sourceTransition hkm) (D.sourceProjection k)
        (D.sourceProjection_comp_sourceTransition hkm) K M ψ :=
  (DerivedPullbackComposition.canonical B S hS).factorHom_comp _ _ _ _ _ _ _
    (D.sourceProjection_comp_sourceTransition hmn) _ _ K M ψ

/-- Two morphisms at a stage with the same derived pullback at a stage `n₁` have the same
derived pullback at every later stage `n ≥ n₁`. -/
theorem map_transition_eq_of_le {n₀ n₁ n : D.LaterIndex} (h₁ : n₀.1 ≤ n₁.1) (h : n₁.1 ≤ n.1)
    {K M : derivedModules B S hS (D.stageSource n₀)} {χ χ' : K ⟶ M}
    (hχ : (smallEtaleDerivedModulePullback B S hS (D.sourceTransition h₁)).map χ =
      (smallEtaleDerivedModulePullback B S hS (D.sourceTransition h₁)).map χ') :
    (smallEtaleDerivedModulePullback B S hS (D.sourceTransition (h₁.trans h))).map χ =
      (smallEtaleDerivedModulePullback B S hS (D.sourceTransition (h₁.trans h))).map χ' := by
  have e := fun ψ : K ⟶ M => (DerivedPullbackComposition.canonical B S hS).factorHom_pullbackMap
    (D.sourceTransition h) (D.sourceTransition h₁) (D.sourceTransition (h₁.trans h))
    (D.sourceTransition_comp_sourceTransition h₁ h) ψ
  rw [← e χ, ← e χ', hχ]

/-- **An isomorphism at the limit between derived pullbacks of `Yₖ`-perfect objects descends
to an isomorphism at a stage**, in a situation whose comparison out of the colimit is fully
faithful: there are `n ≥ k` and an isomorphism `L(f_{nk})^*K ≅ L(f_{nk})^*M` inducing it through
the canonical identifications. -/
theorem exists_iso_stage_of_fullyFaithful (h0DKT : RelativelyPerfectBaseChangeStable B S hS)
    (hff : D.RelativelyPerfectFullyFaithful) (hD : D.IsSchemeLimit) {k : D.LaterIndex}
    (K M : derivedModules B S hS (D.stageSource k))
    (hK : D.IsStagePerfect k K) (hM : D.IsStagePerfect k M)
    (φ : (smallEtaleDerivedModulePullback B S hS (D.sourceProjection k)).obj K ≅
      (smallEtaleDerivedModulePullback B S hS (D.sourceProjection k)).obj M) :
    ∃ (n : D.LaterIndex) (hkn : k.1 ≤ n.1)
      (ψ : (smallEtaleDerivedModulePullback B S hS (D.sourceTransition hkn)).obj K ≅
        (smallEtaleDerivedModulePullback B S hS (D.sourceTransition hkn)).obj M),
      (DerivedPullbackComposition.canonical B S hS).factorHom (D.sourceProjection n)
        (D.sourceTransition hkn) (D.sourceProjection k)
        (D.sourceProjection_comp_sourceTransition hkn) K M ψ.hom = φ.hom := by
  have _ := D.isDirected_laterIndex
  let P := DerivedPullbackComposition.canonical B S hS
  obtain ⟨m₁, h₁, a₁, e₁⟩ := D.exists_factorHom_eq_of_fullyFaithful hff hD K M hK hM φ.hom
  obtain ⟨m₂, h₂, b₁, e₂⟩ := D.exists_factorHom_eq_of_fullyFaithful hff hD M K hM hK φ.inv
  obtain ⟨n₀, hm₁, hm₂⟩ := directed_of (· ≤ ·) m₁ m₂
  have hkn₀ : k.1 ≤ n₀.1 := h₁.trans hm₁
  -- the two morphisms at the common stage `n₀`
  let a := P.factorHom (D.sourceTransition hm₁) (D.sourceTransition h₁)
    (D.sourceTransition hkn₀) (D.sourceTransition_comp_sourceTransition h₁ hm₁) K M a₁
  let b := P.factorHom (D.sourceTransition hm₂) (D.sourceTransition h₂)
    (D.sourceTransition hkn₀) (D.sourceTransition_comp_sourceTransition h₂ hm₂) M K b₁
  have ea : P.factorHom (D.sourceProjection n₀) (D.sourceTransition hkn₀) (D.sourceProjection k)
      (D.sourceProjection_comp_sourceTransition hkn₀) K M a = φ.hom :=
    (D.factorHom_transport h₁ hm₁ K M a₁).trans e₁
  have eb : P.factorHom (D.sourceProjection n₀) (D.sourceTransition hkn₀) (D.sourceProjection k)
      (D.sourceProjection_comp_sourceTransition hkn₀) M K b = φ.inv :=
    (D.factorHom_transport h₂ hm₂ M K b₁).trans e₂
  -- the two composites become identities at the limit, hence at a stage
  have hab := (P.map_comp_eq_map_id_iff _ _ _ (D.sourceProjection_comp_sourceTransition hkn₀)
    a b).2 (by rw [ea, eb]; exact φ.hom_inv_id)
  have hba := (P.map_comp_eq_map_id_iff _ _ _ (D.sourceProjection_comp_sourceTransition hkn₀)
    b a).2 (by rw [ea, eb]; exact φ.inv_hom_id)
  have hK₀ := D.isStagePerfect_transition h0DKT hkn₀ K hK
  have hM₀ := D.isStagePerfect_transition h0DKT hkn₀ M hM
  obtain ⟨n₁, hn₁, e₃⟩ := (hff hD).2 n₀ _ _ hK₀ hK₀ (a ≫ b) (𝟙 _) hab
  obtain ⟨n₂, hn₂, e₄⟩ := (hff hD).2 n₀ _ _ hM₀ hM₀ (b ≫ a) (𝟙 _) hba
  obtain ⟨n, hn₁n, hn₂n⟩ := directed_of (· ≤ ·) n₁ n₂
  have hn₀n : n₀.1 ≤ n.1 := hn₁.trans hn₁n
  have hkn : k.1 ≤ n.1 := hkn₀.trans hn₀n
  have e₃' := D.map_transition_eq_of_le hn₁ hn₁n e₃
  have e₄' := D.map_transition_eq_of_le hn₂ hn₂n e₄
  -- the isomorphism at the stage `n`
  let a' := P.factorHom (D.sourceTransition hn₀n) (D.sourceTransition hkn₀)
    (D.sourceTransition hkn) (D.sourceTransition_comp_sourceTransition hkn₀ hn₀n) K M a
  let b' := P.factorHom (D.sourceTransition hn₀n) (D.sourceTransition hkn₀)
    (D.sourceTransition hkn) (D.sourceTransition_comp_sourceTransition hkn₀ hn₀n) M K b
  exact ⟨n, hkn, ⟨a', b', (P.map_comp_eq_map_id_iff _ _ _ _ a b).1 e₃',
    (P.map_comp_eq_map_id_iff _ _ _ _ b a).1 e₄'⟩,
    (D.factorHom_transport hkn₀ hn₀n K M a).trans ea⟩



section SquareStep

attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

local notation "𝐋 " f => smallEtaleDerivedModulePullback _ _ _ f
local notation "𝐏" => DerivedPullbackComposition.canonical _ _ _

variable {Uo : Subfunctor D.X₀} {V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {fV : V₀ ⟶ D.X₀}
  (hsq : IsElementaryDistinguishedSquare B S hS D.initialSource.2 Uo fV)
  (hfpU : IsFinitePresentation B S hS Uo.ι) (hfpV : IsFinitePresentation B S hS fV)
  (hfpP : IsFinitePresentation B S hS (pullback.fst Uo.ι fV ≫ Uo.ι))

/-- The situation over the open piece `U₀` of an elementary distinguished square of `X₀`. -/
abbrev edsOpenSituation : RelativeDescentSituation B S hS hZ I :=
  D.withSource (D.edsOpenSource hsq hfpU)

/-- The situation over the étale piece `V₀` of an elementary distinguished square of `X₀`. -/
abbrev edsEtaleSituation : RelativeDescentSituation B S hS hZ I :=
  D.withSource (D.edsEtaleSource hsq hfpV)

/-- The situation over the intersection `P₀ = U₀ ×_{X₀} V₀` of an elementary distinguished
square of `X₀`. -/
abbrev edsInterSituation : RelativeDescentSituation B S hS hZ I :=
  D.withSource (D.edsInterSource hsq hfpP)

/-- **The first step of the square step: the restrictions to the two pieces come from a common
stage.**  If every `Y`-perfect object over the limit of the situations over `U₀` and `V₀` comes
from a stage, then for a `Y`-perfect `E` on `X` there are a stage `k` and `Yₖ`-perfect objects
`A` on `Uₖ` and `Bo` on `Vₖ` whose derived pullbacks to the limit are `E|_U` and `E|_V`. -/
theorem exists_stage_of_eds (h0DKT : RelativelyPerfectBaseChangeStable B S hS)
    (hloc : EtaleLocalRelativelyPerfect B S hS)
    (hU : (D.edsOpenSituation hsq hfpU).RelativelyPerfectEssentiallySurjective)
    (hV : (D.edsEtaleSituation hsq hfpV).RelativelyPerfectEssentiallySurjective)
    (hD : D.IsSchemeLimit)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS D.limitSource)))
    (hE : D.IsLimitPerfect E) :
    ∃ (k : D.LaterIndex)
      (A : DerivedCategory (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS ((D.edsOpenSituation hsq hfpU).stageSource k))))
      (Bo : DerivedCategory (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS ((D.edsEtaleSituation hsq hfpV).stageSource k)))),
      (D.edsOpenSituation hsq hfpU).IsStagePerfect k A ∧
      (D.edsEtaleSituation hsq hfpV).IsStagePerfect k Bo ∧
      Nonempty ((𝐋 ((D.edsOpenSituation hsq hfpU).sourceProjection k)).obj A ≅
        (𝐋 (edsOpenHom B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial))).obj E) ∧
      Nonempty ((𝐋 ((D.edsEtaleSituation hsq hfpV).sourceProjection k)).obj Bo ≅
        (𝐋 (edsEtaleHom B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial))).obj
          E) := by
  have _ := D.isDirected_laterIndex
  let DU := D.edsOpenSituation hsq hfpU
  let DV := D.edsEtaleSituation hsq hfpV
  let jU := edsOpenHom B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial)
  let jV := edsEtaleHom B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial)
  have hEU : DU.IsLimitPerfect ((𝐋 jU).obj E) :=
    hloc.1 D.limitStructure jU D.isFlat_limitStructure
      D.isLocallyOfFinitePresentation_limitStructure DU.isFlat_limitStructure
      DU.isLocallyOfFinitePresentation_limitStructure (isEtale_edsOpenHom B S hS _) E hE
  have hEV : DV.IsLimitPerfect ((𝐋 jV).obj E) :=
    hloc.1 D.limitStructure jV D.isFlat_limitStructure
      D.isLocallyOfFinitePresentation_limitStructure DV.isFlat_limitStructure
      DV.isLocallyOfFinitePresentation_limitStructure (isEtale_edsEtaleHom B S hS _) E hE
  obtain ⟨iU, AU, hAU, ⟨αU⟩⟩ := hU (D.isSchemeLimit_withSource _ hD) _ hEU
  obtain ⟨iV, BV, hBV, ⟨αV⟩⟩ := hV (D.isSchemeLimit_withSource _ hD) _ hEV
  obtain ⟨k, hik, hjk⟩ := D.isDirected_laterIndex.directed (r := (· ≤ ·)) iU iV
  exact ⟨k, _, _, DU.isStagePerfect_transition h0DKT hik AU hAU,
    DV.isStagePerfect_transition h0DKT hjk BV hBV,
    ⟨((𝐏).iso (DU.sourceProjection k) (DU.sourceTransition hik) (DU.sourceProjection iU)
      (DU.sourceProjection_comp_sourceTransition hik)).app AU ≪≫ αU⟩,
    ⟨((𝐏).iso (DV.sourceProjection k) (DV.sourceTransition hjk) (DV.sourceProjection iV)
      (DV.sourceProjection_comp_sourceTransition hjk)).app BV ≪≫ αV⟩⟩

/-- **The second step of the square step: the overlap isomorphism descends to a stage.**  For
`Yₖ`-perfect objects `A` on `Uₖ` and `Bo` on `Vₖ` identified with `E|_U` and `E|_V` at the
limit, full faithfulness of the situation over `P₀` gives a stage `n ≥ k` and an isomorphism of
the restrictions of `A` and `Bo` to `Pₙ` inducing the identification of `A|_P` with `Bo|_P` at
the limit. -/
theorem exists_descended_iso_of_eds (h0DKT : RelativelyPerfectBaseChangeStable B S hS)
    (hloc : EtaleLocalRelativelyPerfect B S hS)
    (hP : (D.edsInterSituation hsq hfpP).RelativelyPerfectFullyFaithful) (hD : D.IsSchemeLimit)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS D.limitSource)))
    (k : D.LaterIndex)
    (A : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS ((D.edsOpenSituation hsq hfpU).stageSource k))))
    (Bo : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS ((D.edsEtaleSituation hsq hfpV).stageSource k))))
    (hA : (D.edsOpenSituation hsq hfpU).IsStagePerfect k A)
    (hB : (D.edsEtaleSituation hsq hfpV).IsStagePerfect k Bo)
    (αU : (𝐋 ((D.edsOpenSituation hsq hfpU).sourceProjection k)).obj A ≅
      (𝐋 (edsOpenHom B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial))).obj E)
    (αV : (𝐋 ((D.edsEtaleSituation hsq hfpV).sourceProjection k)).obj Bo ≅
      (𝐋 (edsEtaleHom B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial))).obj E) :
    ∃ (n : D.LaterIndex) (hkn : k.1 ≤ n.1)
      (ψ : (𝐋 ((D.edsInterSituation hsq hfpP).sourceTransition hkn)).obj
          ((𝐋 (edsFst B S hS (edsPreimage (W₀ := D.initialSource) hsq (D.stageToInitial k)))).obj
            A) ≅
        (𝐋 ((D.edsInterSituation hsq hfpP).sourceTransition hkn)).obj
          ((𝐋 (edsSnd B S hS (edsPreimage (W₀ := D.initialSource) hsq (D.stageToInitial k)))).obj
            Bo)),
      (𝐏).factorHom ((D.edsInterSituation hsq hfpP).sourceProjection n)
          ((D.edsInterSituation hsq hfpP).sourceTransition hkn)
          ((D.edsInterSituation hsq hfpP).sourceProjection k)
          ((D.edsInterSituation hsq hfpP).sourceProjection_comp_sourceTransition hkn) _ _ ψ.hom =
        (((𝐏).squareIso (edsFst B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial))
            ((D.edsOpenSituation hsq hfpU).sourceProjection k)
            ((D.edsInterSituation hsq hfpP).sourceProjection k)
            (edsFst B S hS (edsPreimage (W₀ := D.initialSource) hsq (D.stageToInitial k)))
            (edsFst_comp_edsPreimageOpenMap (W₀ := D.initialSource) hsq (D.stageToInitial k)
              D.limitToInitial (D.sourceProjection k)
              (D.sourceProjection_comp_stageToInitial k))).app A ≪≫
          (𝐋 (edsFst B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial))).mapIso
            αU ≪≫
          ((𝐏).squareIso (edsSnd B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial))
            (edsEtaleHom B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial))
            (edsFst B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial))
            (edsOpenHom B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial))
            (isPullback_edsInter B S hS _).flip.w).app E ≪≫
          (𝐋 (edsSnd B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial))).mapIso
            αV.symm ≪≫
          (((𝐏).squareIso (edsSnd B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial))
            ((D.edsEtaleSituation hsq hfpV).sourceProjection k)
            ((D.edsInterSituation hsq hfpP).sourceProjection k)
            (edsSnd B S hS (edsPreimage (W₀ := D.initialSource) hsq (D.stageToInitial k)))
            (edsSnd_comp_edsPreimageEtaleMap (W₀ := D.initialSource) hsq (D.stageToInitial k)
              D.limitToInitial (D.sourceProjection k)
              (D.sourceProjection_comp_stageToInitial k))).app Bo).symm).hom := by
  let DU := D.edsOpenSituation hsq hfpU
  let DV := D.edsEtaleSituation hsq hfpV
  let DP := D.edsInterSituation hsq hfpP
  let fstk := edsFst B S hS (edsPreimage (W₀ := D.initialSource) hsq (D.stageToInitial k))
  let sndk := edsSnd B S hS (edsPreimage (W₀ := D.initialSource) hsq (D.stageToInitial k))
  have hKA : DP.IsStagePerfect k ((𝐋 fstk).obj A) := by
    have h : fstk ≫ DU.stageStructure k = DP.stageStructure k :=
      ObjectProperty.hom_ext _ (Category.assoc _ _ _).symm
    exact isPerfectAlong_congr h (h.symm ▸ DP.isFlat_stageStructure k)
      (h.symm ▸ DP.isLocallyOfFinitePresentation_stageStructure k) _ _
      (hloc.1 (DU.stageStructure k) fstk (DU.isFlat_stageStructure k)
        (DU.isLocallyOfFinitePresentation_stageStructure k) _ _ (isEtale_edsFst B S hS _) A hA)
  have hKB : DP.IsStagePerfect k ((𝐋 sndk).obj Bo) := by
    have h : sndk ≫ DV.stageStructure k = DP.stageStructure k := by
      refine ObjectProperty.hom_ext _ ?_
      have w := congrArg (fun φ => φ.hom) (isPullback_edsInter B S hS
        (edsPreimage (W₀ := D.initialSource) hsq (D.stageToInitial k))).w
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ D.toYᵢ k.1 k.2) w.symm)
    exact isPerfectAlong_congr h (h.symm ▸ DP.isFlat_stageStructure k)
      (h.symm ▸ DP.isLocallyOfFinitePresentation_stageStructure k) _ _
      (hloc.1 (DV.stageStructure k) sndk (DV.isFlat_stageStructure k)
        (DV.isLocallyOfFinitePresentation_stageStructure k) _ _ (isEtale_edsSnd B S hS _) Bo hB)
  let fst' := edsFst B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial)
  let snd' := edsSnd B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial)
  exact DP.exists_iso_stage_of_fullyFaithful h0DKT hP (D.isSchemeLimit_withSource _ hD) _ _ hKA
    hKB (((𝐏).squareIso fst' (DU.sourceProjection k) (DP.sourceProjection k) fstk
        (edsFst_comp_edsPreimageOpenMap (W₀ := D.initialSource) hsq (D.stageToInitial k)
          D.limitToInitial (D.sourceProjection k) (D.sourceProjection_comp_stageToInitial k))).app
          A ≪≫
      (𝐋 fst').mapIso αU ≪≫
      ((𝐏).squareIso snd' (edsEtaleHom B S hS (edsPreimage (W₀ := D.initialSource) hsq
          D.limitToInitial)) fst'
        (edsOpenHom B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial))
        (isPullback_edsInter B S hS _).flip.w).app E ≪≫
      (𝐋 snd').mapIso αV.symm ≪≫
      (((𝐏).squareIso snd' (DV.sourceProjection k) (DP.sourceProjection k) sndk
        (edsSnd_comp_edsPreimageEtaleMap (W₀ := D.initialSource) hsq (D.stageToInitial k)
          D.limitToInitial (D.sourceProjection k) (D.sourceProjection_comp_stageToInitial k))).app
          Bo).symm)

/-- **The square step of the essential surjectivity in Stacks 0DKW.**  Let
`(U₀ ⊆ X₀, V₀ ⟶ X₀)` be an elementary distinguished square of `X₀` whose three pieces are of
finite presentation over `X₀`.  If every `Y`-perfect object over the limit of the situations
over `U₀` and over `V₀` comes from a stage, and the comparison out of the colimit is fully
faithful for the situation over `P₀ = U₀ ×_{X₀} V₀`, then every `Y`-perfect object of `D(𝒪_X)`
comes from a stage.  The inputs are Stacks 0DKT (`h0DKT`, proved by
`AlgebraicGeometry.Space.relativelyPerfectBaseChangeStable`), used to move objects to later
stages, and the étale locality of relative perfectness (`hloc`, a consequence of Stacks 0DKQ,
proved by `AlgebraicGeometry.Space.etaleLocalRelativelyPerfect`). -/
theorem relativelyPerfectEssentiallySurjective_of_eds
    (h0DKT : RelativelyPerfectBaseChangeStable B S hS)
    (hloc : EtaleLocalRelativelyPerfect B S hS)
    (hU : (D.edsOpenSituation hsq hfpU).RelativelyPerfectEssentiallySurjective)
    (hV : (D.edsEtaleSituation hsq hfpV).RelativelyPerfectEssentiallySurjective)
    (hP : (D.edsInterSituation hsq hfpP).RelativelyPerfectFullyFaithful) :
    D.RelativelyPerfectEssentiallySurjective := by
  intro hD E₀ hE
  obtain ⟨E, hE₀⟩ : ∃ E : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS D.limitSource)), E = E₀ := ⟨E₀, rfl⟩
  subst hE₀
  obtain ⟨k, A, Bo, hA, hB, ⟨αU⟩, ⟨αV⟩⟩ :=
    D.exists_stage_of_eds hsq hfpU hfpV h0DKT hloc hU hV hD E hE
  obtain ⟨n, hkn, ψ, hψ⟩ :=
    D.exists_descended_iso_of_eds hsq hfpU hfpV hfpP h0DKT hloc hP hD E k A Bo hA hB αU αV
  obtain ⟨F, fU, gV, ⟨eF⟩⟩ := exists_glue_of_descended_iso
    (edsPreimage (W₀ := D.initialSource) hsq (D.stageToInitial n))
    (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial)
    (D.sourceProjection n) ((D.edsOpenSituation hsq hfpU).sourceProjection n)
    ((D.edsEtaleSituation hsq hfpV).sourceProjection n)
    ((D.edsInterSituation hsq hfpP).sourceProjection n)
    (edsPreimageOpenMap_comp (W₀ := D.initialSource) hsq _ _ (D.sourceProjection n)
      (D.sourceProjection_comp_stageToInitial n))
    (edsPreimageEtaleMap_comp (W₀ := D.initialSource) hsq _ _ (D.sourceProjection n)
      (D.sourceProjection_comp_stageToInitial n))
    (edsFst_comp_edsPreimageOpenMap (W₀ := D.initialSource) hsq _ _ (D.sourceProjection n)
      (D.sourceProjection_comp_stageToInitial n))
    (edsSnd_comp_edsPreimageEtaleMap (W₀ := D.initialSource) hsq _ _ (D.sourceProjection n)
      (D.sourceProjection_comp_stageToInitial n))
    _ _ ((D.edsOpenSituation hsq hfpU).sourceTransition hkn)
    ((D.edsEtaleSituation hsq hfpV).sourceTransition hkn)
    ((D.edsInterSituation hsq hfpP).sourceTransition hkn)
    (edsFst_comp_edsPreimageOpenMap (W₀ := D.initialSource) hsq _ _ (D.sourceTransition hkn)
      (D.sourceTransition_comp_stageToInitial hkn))
    (edsSnd_comp_edsPreimageEtaleMap (W₀ := D.initialSource) hsq _ _ (D.sourceTransition hkn)
      (D.sourceTransition_comp_stageToInitial hkn))
    ((D.edsOpenSituation hsq hfpU).sourceProjection k)
    ((D.edsEtaleSituation hsq hfpV).sourceProjection k)
    ((D.edsInterSituation hsq hfpP).sourceProjection k) _ _
    ((D.edsOpenSituation hsq hfpU).sourceProjection_comp_sourceTransition hkn)
    ((D.edsEtaleSituation hsq hfpV).sourceProjection_comp_sourceTransition hkn)
    ((D.edsInterSituation hsq hfpP).sourceProjection_comp_sourceTransition hkn) E A Bo αU αV ψ hψ
  refine ⟨n, F, ?_, ⟨eF⟩⟩
  exact hloc.2 (D.stageStructure n) (D.isFlat_stageStructure n)
    (D.isLocallyOfFinitePresentation_stageStructure n)
    (edsPreimage (W₀ := D.initialSource) hsq (D.stageToInitial n))
    ((D.edsOpenSituation hsq hfpU).isFlat_stageStructure n)
    ((D.edsOpenSituation hsq hfpU).isLocallyOfFinitePresentation_stageStructure n)
    ((D.edsEtaleSituation hsq hfpV).isFlat_stageStructure n)
    ((D.edsEtaleSituation hsq hfpV).isLocallyOfFinitePresentation_stageStructure n) F
    (isPerfectAlong_of_iso _ _ _ fU.symm
      ((D.edsOpenSituation hsq hfpU).isStagePerfect_transition h0DKT hkn A hA))
    (isPerfectAlong_of_iso _ _ _ gV.symm
      ((D.edsEtaleSituation hsq hfpV).isStagePerfect_transition h0DKT hkn Bo hB))

end SquareStep

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
