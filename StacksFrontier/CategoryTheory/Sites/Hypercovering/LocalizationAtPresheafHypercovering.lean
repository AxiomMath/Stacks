module

public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.LocalizationAtPresheaf
public import StacksFrontier.CategoryTheory.Sites.Topos.PresheafLocalization

/-!
# Hypercoverings of a presheaf are hypercoverings of the localized site

Let `C` be a site, given by a pretopology `J`, with equalizers and fibre products, and let `G`
be a presheaf of sets on `C`. Stacks 09X6 asserts that a hypercovering of `G` in the sense of
Stacks 09VU is the same thing as a hypercovering of the site `C/G`, the localization of `C` at
`G` defined exactly as in Stacks 0791 (`CostructuredArrow yoneda G`, with the coverings coming
from coverings of `C`). This file proves it:

`HypercoveringOf J G ≃ HypercoveringOfTerminal J_G`

for every pretopology `J_G` on `C/G` generating the topology of Stacks 0791, and in particular
for the canonical one `localizationPretopology J G`.

The underlying correspondence is `SR(C/G) ≌ SR(C)/G` of
`StacksFrontier.CategoryTheory.Sites.Hypercovering.LocalizationAtPresheaf`: a simplicial object of
`SR(C/G)` is a simplicial object `K` of `SR(C)` with an augmentation `F(K) ⟶ G`. What has to be
checked is that the three conditions of Stacks 09VU correspond, and the proof is the one the
source leaves to the reader.

* A morphism `φ' : P' ⟶ Q'` of presheaves on `C/G` is locally surjective exactly when the
  corresponding morphism `φ` of presheaves on `C` is, as soon as the sections of `P'` and `Q'`
  over `(U, s)` are the sections of `P` and `Q` over `U` lying over `s`
  (`isLocallySurjective_iff_of_sections`). The engine is that a sieve on `(U, s)` covers exactly
  when its image in `C` covers (Stacks 0791), together with the unique lifting of morphisms of
  `C` to `C/G`.
* Conditions (1) and (2) are statements about the augmentation and about fibre products over
  `G`; over `C/G` the augmentation goes to the final presheaf, and fibre products over `G` become
  products. The sections of the presheaf `F(X)` of an object of `SR(C/G)` over `(U, s)` are the
  sections of `F(X)` over `U` on which the augmentation takes the value `s`
  (`secForget_surjective`, `secForget_injective`).
* Condition (3) involves the coskeleta, which are computed in `SR(C/G)` and in `SR(C)`
  respectively. The functor `SR(C/G) ⥤ SR(C)` preserves connected limits, hence the coskeleta
  in positive degree, compatibly with the units (`exists_coskAdj_unit_comp_eq`).

## Main definitions

* `toHypercoveringOf` and `ofHypercoveringOf`: the two directions of the correspondence.
* `hypercoveringEquiv`: the correspondence as an equivalence of types.
* `localizationPretopology`: the pretopology on `C/G` whose covering families are those whose
  generated sieve covers in the topology of Stacks 0791.

## Main results

* `isLocallySurjective_iff_of_sections`: transfer of local surjectivity between `C` and `C/G`.
* `exists_coskAdj_unit_comp_eq`: a functor preserving the limits defining a coskeleton commutes
  with it, compatibly with the unit of the coskeleton adjunction.
* `hypercoveringOfEquivLocalization`: **Stacks 09X6**, a hypercovering of `G` is the same thing as
  a hypercovering of the site `C/G`.

## Implementation notes

Stacks 0791 describes the coverings of `C/G` as the families `{(U_i, s_i) ⟶ (U, s)}` such that
`{U_i ⟶ U}` covers `U`. A pretopology in Mathlib must be stable under the *chosen* pullbacks,
which those families need not be unless the coverings of `C` are closed under isomorphic
replacement; the hypercovering conditions, however, only involve the generated Grothendieck
topology, namely `(CostructuredArrow.proj yoneda G).restrictedTopology J.toGrothendieck`
(`Stacks.Sites.PresheafLocalization.mem_restrictedTopology_iff`). The correspondence is
therefore stated for any pretopology on `C/G` generating that topology, and specialized to the
pretopology of all families generating a covering sieve.

## References

* [Stacks Project, Tag 09X6](https://stacks.math.columbia.edu/tag/09X6)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe t t' w v u

namespace Stacks.CategoryTheory.Hypercovering.LocalizationAtPresheaf

variable {C : Type u} [Category.{v} C] {G : Cᵒᵖ ⥤ Type v}

/-! ### Transfer of local surjectivity -/

section Transfer

variable (J : GrothendieckTopology C)
  (K : GrothendieckTopology (CostructuredArrow (yoneda (C := C)) G))
  (hK : ∀ (X : CostructuredArrow (yoneda (C := C)) G) (S : Sieve X),
    S ∈ K X ↔ S.functorPushforward (CostructuredArrow.proj yoneda G) ∈ J X.left)

include hK in
/-- **Local surjectivity on `C/G` is local surjectivity on `C`.** Let `φ' : P' ⟶ Q'` be a
morphism of presheaves on `C/G` and `φ : P ⟶ Q` one of presheaves on `C`, related by maps
`eP`, `eQ` from the sections over `(U, s)` to the sections over `U`, such that `eQ` is natural,
`φ` and `φ'` correspond, every section of `Q` lies in the image of `eQ` over some `(U, s)`, and a
section of `P` whose image is the image of a section `q` of `Q'` lifts to a preimage of `q`.
Then `φ'` is locally surjective exactly when `φ` is. -/
theorem isLocallySurjective_iff_of_sections {P Q : Cᵒᵖ ⥤ Type t} (φ : P ⟶ Q)
    {P' Q' : (CostructuredArrow (yoneda (C := C)) G)ᵒᵖ ⥤ Type t'} (φ' : P' ⟶ Q')
    (eP : ∀ Z : CostructuredArrow (yoneda (C := C)) G, P'.obj (op Z) → P.obj (op Z.left))
    (eQ : ∀ Z : CostructuredArrow (yoneda (C := C)) G, Q'.obj (op Z) → Q.obj (op Z.left))
    (hnat : ∀ {Z Z' : CostructuredArrow (yoneda (C := C)) G} (f : Z' ⟶ Z) (q : Q'.obj (op Z)),
      eQ Z' (Q'.map f.op q) = Q.map f.left.op (eQ Z q))
    (hcomp : ∀ (Z : CostructuredArrow (yoneda (C := C)) G) (p : P'.obj (op Z)),
      φ.app _ (eP Z p) = eQ Z (φ'.app _ p))
    (hsurj : ∀ (U : C) (q : Q.obj (op U)), ∃ (s : yoneda.obj U ⟶ G)
      (q' : Q'.obj (op (CostructuredArrow.mk s))), eQ _ q' = q)
    (hlift : ∀ (Z : CostructuredArrow (yoneda (C := C)) G) (p : P.obj (op Z.left))
      (q : Q'.obj (op Z)), φ.app _ p = eQ Z q → ∃ p' : P'.obj (op Z), φ'.app _ p' = q) :
    Presheaf.IsLocallySurjective K φ' ↔ Presheaf.IsLocallySurjective J φ := by
  refine ⟨fun h ↦ ⟨fun {U} q ↦ ?_⟩, fun h ↦ ⟨fun {Z} q ↦ ?_⟩⟩
  · obtain ⟨s, q', rfl⟩ := hsurj U q
    have hmem := (hK _ _).1 (Presheaf.imageSieve_mem K φ' q')
    refine J.superset_covering ?_ hmem
    rintro V g ⟨Z, f, k, ⟨p', hp'⟩, rfl⟩
    refine ⟨P.map k.op (eP Z p'), ?_⟩
    exact (NatTrans.naturality_apply φ k.op (eP Z p')).trans
      ((congrArg (Q.map k.op) ((hcomp Z p').trans (congrArg (eQ Z) hp'))).trans
        ((congrArg (Q.map k.op) (hnat f q')).trans
          (Q.map_comp_apply f.left.op k.op _).symm))
  · rw [hK]
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J φ (eQ Z q))
    rintro V g ⟨p, hp⟩
    refine (Stacks.Topos.Localized.mem_functorPushforward_proj_iff G _
      (Stacks.Topos.Localized.liftHom G Z g)).2 ?_
    exact hlift _ p (Q'.map (Stacks.Topos.Localized.liftHom G Z g).op q) (by rwa [hnat])

end Transfer


/-! ### Sections of the presheaf of an object of `SR(C/G)` -/

section Sections

variable (G)

/-- The functor `forgetSR : SR(C/G) ⥤ SR(C)` is faithful. -/
instance faithful_forgetSR : (forgetSR.{w} G).Faithful :=
  inferInstanceAs (toOver G ⋙ CostructuredArrow.proj _ _).Faithful

/-- A section of `F(X)` over `(U, s)`, for `X` an object of `SR(C/G)`, read as a section of
`F(forgetSR X)` over `U`. -/
def secForget (X : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G))
    (Z : CostructuredArrow (yoneda (C := C)) G)
    (z : ((associatedPresheafFunctor.{v}).obj X).obj (op Z)) :
    ((associatedPresheafFunctor.{v}).obj ((forgetSR G).obj X)).obj (op Z.left) :=
  (sectionEquiv ((forgetSR G).obj X) Z.left).symm
    ((forgetSR G).map (sectionEquiv X Z z) : (FormalCoproduct.incl C).obj Z.left ⟶ _)

/-- `secForget` on the section given by a component map. -/
lemma secForget_symm_fromIncl (X : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G))
    {Z : CostructuredArrow (yoneda (C := C)) G} (i : X.I) (k : Z ⟶ X.obj i) :
    secForget G X Z ((sectionEquiv X Z).symm (FormalCoproduct.Hom.fromIncl i k)) =
      (sectionEquiv ((forgetSR G).obj X) Z.left).symm (FormalCoproduct.Hom.fromIncl i k.left) := by
  unfold secForget
  rw [Equiv.apply_symm_apply]
  rfl

/-- `secForget` commutes with the maps of presheaves induced by a morphism of `SR(C/G)`. -/
lemma secForget_map {X Y : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)}
    (f : X ⟶ Y) (Z : CostructuredArrow (yoneda (C := C)) G)
    (z : ((associatedPresheafFunctor.{v}).obj X).obj (op Z)) :
    secForget G Y Z (((associatedPresheafFunctor.{v}).map f).app _ z) =
      ((associatedPresheafFunctor.{v}).map ((forgetSR G).map f)).app _ (secForget G X Z z) := by
  unfold secForget
  rw [sectionEquiv_map, Functor.map_comp]
  exact sectionEquiv_symm_postcomp _ _ Z.left ((forgetSR G).map f)
    ((forgetSR G).map (sectionEquiv X Z z))

/-- `secForget` commutes with restriction along a morphism `Z' ⟶ Z` of `C/G`. -/
lemma secForget_restrict (X : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G))
    {Z Z' : CostructuredArrow (yoneda (C := C)) G} (g : Z' ⟶ Z)
    (z : ((associatedPresheafFunctor.{v}).obj X).obj (op Z)) :
    secForget G X Z' (((associatedPresheafFunctor.{v}).obj X).map g.op z) =
      ((associatedPresheafFunctor.{v}).obj ((forgetSR G).obj X)).map g.left.op
        (secForget G X Z z) := by
  unfold secForget
  rw [sectionEquiv_restrict, Functor.map_comp]
  exact sectionEquiv_symm_precomp ((forgetSR G).obj X) g.left
    ((forgetSR G).map (sectionEquiv X Z z))

/-- The augmentation of `forgetSR X` takes the value `s` on a section coming from `(U, s)`. -/
lemma augmentationOf_secForget
    (X : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G))
    (Z : CostructuredArrow (yoneda (C := C)) G)
    (z : ((associatedPresheafFunctor.{v}).obj X).obj (op Z)) :
    (augmentationOf G X).app _ (secForget G X Z z) = ULift.up (yonedaEquiv Z.hom) := by
  obtain ⟨s, rfl⟩ := (sectionEquiv X Z).symm.surjective z
  rw [← s.fromIncl_asSigma, secForget_symm_fromIncl]
  refine (app_fromIncl (augmentationOf G X) s.asSigma.1 s.asSigma.2.left).trans ?_
  congr 1
  refine (congrArg (G.map s.asSigma.2.left.op) (elementOf_augmentationOf G X _)).trans ?_
  rw [yonedaEquiv_naturality, CostructuredArrow.w]

/-- A section of `F(forgetSR X)` over `U` on which the augmentation takes the value `s` comes
from a section of `F(X)` over `(U, s)`. -/
lemma secForget_surjective (X : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G))
    (Z : CostructuredArrow (yoneda (C := C)) G)
    (p : ((associatedPresheafFunctor.{v}).obj ((forgetSR G).obj X)).obj (op Z.left))
    (hp : (augmentationOf G X).app _ p = ULift.up (yonedaEquiv Z.hom)) :
    ∃ z, secForget G X Z z = p := by
  obtain ⟨s, rfl⟩ := (sectionEquiv ((forgetSR G).obj X) Z.left).symm.surjective p
  rw [← s.fromIncl_asSigma] at hp ⊢
  replace hp := (app_fromIncl (augmentationOf G X) s.asSigma.1 s.asSigma.2).symm.trans hp
  have hw : yoneda.map s.asSigma.2 ≫ (X.obj s.asSigma.1).hom = Z.hom :=
    yonedaEquiv.injective <|
      (yonedaEquiv_naturality (X.obj s.asSigma.1).hom s.asSigma.2).symm.trans
        ((congrArg (G.map s.asSigma.2.op) (elementOf_augmentationOf G X s.asSigma.1).symm).trans
          (congrArg ULift.down hp))
  exact ⟨_, secForget_symm_fromIncl G X s.asSigma.1 (CostructuredArrow.homMk s.asSigma.2 hw)⟩

/-- `secForget` is injective: distinct sections of `F(X)` over `(U, s)` give distinct sections
of `F(forgetSR X)` over `U`. -/
lemma secForget_injective (X : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G))
    (Z : CostructuredArrow (yoneda (C := C)) G) :
    Function.Injective (secForget G X Z) := by
  intro z₁ z₂ h
  unfold secForget at h
  exact (sectionEquiv X Z).injective
    ((forgetSR G).map_injective ((sectionEquiv ((forgetSR G).obj X) Z.left).symm.injective h))

/-- The augmentation of a section over `U` takes the value of some `s : U ⟶ G`. -/
private lemma exists_augmentationOf_eq_up
    (X : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)) {U : C}
    (q : ((associatedPresheafFunctor.{v}).obj ((forgetSR G).obj X)).obj (op U)) :
    ∃ s : yoneda.obj U ⟶ G, (augmentationOf G X).app _ q = ULift.up (yonedaEquiv s) :=
  ⟨yonedaEquiv.symm ((augmentationOf G X).app _ q).down, by
    rw [Equiv.apply_symm_apply]
    rfl⟩

/-- If the image of `p` under a morphism is `secForget` of a section over `(U, s)`, then the
augmentation of `p` takes the value `s`. -/
private lemma augmentationOf_eq_of_map_eq
    {X Y : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)} (u : X ⟶ Y)
    (Z : CostructuredArrow (yoneda (C := C)) G)
    (p : ((associatedPresheafFunctor.{v}).obj ((forgetSR G).obj X)).obj (op Z.left))
    (q : ((associatedPresheafFunctor.{v}).obj Y).obj (op Z))
    (hp : ((associatedPresheafFunctor.{v}).map ((forgetSR G).map u)).app _ p = secForget G Y Z q) :
    (augmentationOf G X).app _ p = ULift.up (yonedaEquiv Z.hom) := by
  rw [← map_comp_augmentationOf G u, NatTrans.comp_app, ConcreteCategory.comp_apply, hp,
    augmentationOf_secForget]

/-- A section of the final presheaf, lifted. -/
def liftedTerminalSection (Z : CostructuredArrow (yoneda (C := C)) G) :
    (liftedPresheaf.{v, w} (⊤_ ((CostructuredArrow (yoneda (C := C)) G)ᵒᵖ ⥤ Type v))).obj
      (op Z) :=
  (isTerminal_liftedTerminal.{w}.from
    ((Functor.const _).obj PUnit.{max v w + 1})).app (op Z) PUnit.unit

end Sections

/-! ### The three conditions of Stacks 09VU -/

section Conditions

variable [HasPullbacks C] (J : Pretopology C)
  (J' : Pretopology (CostructuredArrow (yoneda (C := C)) G))
  (hJ' : J'.toGrothendieck =
    (CostructuredArrow.proj yoneda G).restrictedTopology J.toGrothendieck)

include hJ' in
/-- A sieve on `(U, s)` covers for `J'` exactly when its image in `C` covers `U` for `J`. -/
lemma mem_toGrothendieck_iff (X : CostructuredArrow (yoneda (C := C)) G) (S : Sieve X) :
    S ∈ J'.toGrothendieck X ↔
      S.functorPushforward (CostructuredArrow.proj yoneda G) ∈ J.toGrothendieck X.left := by
  rw [hJ']
  exact Stacks.Sites.PresheafLocalization.mem_restrictedTopology_iff G J.toGrothendieck X S

include hJ' in
/-- **Condition (1) of Stacks 09VU.** The augmentation of an object `X` of `SR(C/G)` to the final
presheaf of `C/G` is locally surjective exactly when the augmentation of `forgetSR X` to `G` is. -/
theorem isLocallySurjective_toTerminal_iff
    (X : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G))
    (a : (associatedPresheafFunctor.{v}).obj X ⟶
      liftedPresheaf.{v, w} (⊤_ ((CostructuredArrow (yoneda (C := C)) G)ᵒᵖ ⥤ Type v))) :
    Presheaf.IsLocallySurjective J'.toGrothendieck a ↔
      Presheaf.IsLocallySurjective J.toGrothendieck (augmentationOf G X) := by
  refine isLocallySurjective_iff_of_sections J.toGrothendieck J'.toGrothendieck
    (mem_toGrothendieck_iff J J' hJ') (augmentationOf G X) a (secForget G X)
    (fun Z _ ↦ ULift.up (yonedaEquiv Z.hom)) ?_ (augmentationOf_secForget G X) ?_ ?_
  · intro Z Z' f q
    show ULift.up (yonedaEquiv Z'.hom) = ULift.up (G.map f.left.op (yonedaEquiv Z.hom))
    rw [yonedaEquiv_naturality, CostructuredArrow.w]
  · intro U q
    refine ⟨yonedaEquiv.symm q.down, liftedTerminalSection G _, ?_⟩
    show ULift.up (yonedaEquiv (yonedaEquiv.symm q.down)) = q
    rw [Equiv.apply_symm_apply]
    rfl
  · intro Z p q hp
    obtain ⟨z, rfl⟩ := secForget_surjective G X Z p hp
    exact ⟨z, (subsingleton_liftedTerminal.{w} Z).elim _ _⟩

include hJ' in
/-- **Condition (3) of Stacks 09VU, for one morphism.** The image under `F` of a morphism of
`SR(C/G)` is locally surjective exactly when the image under `F` of the underlying morphism of
`SR(C)` is. -/
theorem isLocallySurjective_map_iff
    {X Y : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)} (u : X ⟶ Y) :
    Presheaf.IsLocallySurjective J'.toGrothendieck ((associatedPresheafFunctor.{v}).map u) ↔
      Presheaf.IsLocallySurjective J.toGrothendieck
        ((associatedPresheafFunctor.{v}).map ((forgetSR G).map u)) := by
  refine isLocallySurjective_iff_of_sections J.toGrothendieck J'.toGrothendieck
    (mem_toGrothendieck_iff J J' hJ') _ _ (secForget G X) (secForget G Y)
    (fun f q ↦ secForget_restrict G Y f q) (fun Z p ↦ (secForget_map G u Z p).symm) ?_ ?_
  · intro U q
    obtain ⟨s, hs⟩ := exists_augmentationOf_eq_up G Y q
    exact ⟨s, secForget_surjective G Y (.mk s) q hs⟩
  · intro Z p q hp
    have hp' := augmentationOf_eq_of_map_eq G u Z p q hp
    obtain ⟨z, rfl⟩ := secForget_surjective G X Z p hp'
    refine ⟨z, secForget_injective G Y Z ?_⟩
    rwa [secForget_map]

/-- The sections of a fibre product of presheaves of types are the compatible pairs: two of them
agree as soon as their two projections do. -/
lemma pullback_app_ext {A : Type*} [Category A] {P₁ P₂ T : Aᵒᵖ ⥤ Type t} (f₁ : P₁ ⟶ T)
    (f₂ : P₂ ⟶ T) {X : Aᵒᵖ} {x y : (pullback f₁ f₂).obj X}
    (h₁ : (pullback.fst f₁ f₂).app X x = (pullback.fst f₁ f₂).app X y)
    (h₂ : (pullback.snd f₁ f₂).app X x = (pullback.snd f₁ f₂).app X y) : x = y :=
  Types.ext_of_isPullback ((IsPullback.of_hasPullback f₁ f₂).map ((evaluation _ _).obj X)) h₁ h₂

/-- The sections of a fibre product of presheaves of types are the compatible pairs: every
compatible pair is the pair of projections of a section. -/
lemma pullback_app_exists {A : Type*} [Category A] {P₁ P₂ T : Aᵒᵖ ⥤ Type t} (f₁ : P₁ ⟶ T)
    (f₂ : P₂ ⟶ T) {X : Aᵒᵖ} (x₁ : P₁.obj X) (x₂ : P₂.obj X) (h : f₁.app X x₁ = f₂.app X x₂) :
    ∃ x : (pullback f₁ f₂).obj X,
      (pullback.fst f₁ f₂).app X x = x₁ ∧ (pullback.snd f₁ f₂).app X x = x₂ :=
  Types.exists_of_isPullback ((IsPullback.of_hasPullback f₁ f₂).map ((evaluation _ _).obj X))
    x₁ x₂ h

/-- The first projection of `pullback.lift g₁ g₂ h`, evaluated on a section, is `g₁` of it. -/
lemma pullback_lift_fst_app {A : Type*} [Category A] {P P₁ P₂ T : Aᵒᵖ ⥤ Type t} {f₁ : P₁ ⟶ T}
    {f₂ : P₂ ⟶ T} (g₁ : P ⟶ P₁) (g₂ : P ⟶ P₂) (h : g₁ ≫ f₁ = g₂ ≫ f₂) (X : Aᵒᵖ) (p : P.obj X) :
    (pullback.fst f₁ f₂).app X ((pullback.lift g₁ g₂ h).app X p) = g₁.app X p :=
  ConcreteCategory.congr_hom (congr_app (pullback.lift_fst g₁ g₂ h) X) p

/-- The second projection of `pullback.lift g₁ g₂ h`, evaluated on a section, is `g₂` of it. -/
lemma pullback_lift_snd_app {A : Type*} [Category A] {P P₁ P₂ T : Aᵒᵖ ⥤ Type t} {f₁ : P₁ ⟶ T}
    {f₂ : P₂ ⟶ T} (g₁ : P ⟶ P₁) (g₂ : P ⟶ P₂) (h : g₁ ≫ f₁ = g₂ ≫ f₂) (X : Aᵒᵖ) (p : P.obj X) :
    (pullback.snd f₁ f₂).app X ((pullback.lift g₁ g₂ h).app X p) = g₂.app X p :=
  ConcreteCategory.congr_hom (congr_app (pullback.lift_snd g₁ g₂ h) X) p

/-- The two projections of a section of a fibre product of presheaves of types have the same
image in the base. -/
lemma pullback_condition_app {A : Type*} [Category A] {P₁ P₂ T : Aᵒᵖ ⥤ Type t} (f₁ : P₁ ⟶ T)
    (f₂ : P₂ ⟶ T) (X : Aᵒᵖ) (x : (pullback f₁ f₂).obj X) :
    f₁.app X ((pullback.fst f₁ f₂).app X x) = f₂.app X ((pullback.snd f₁ f₂).app X x) :=
  ConcreteCategory.congr_hom (congr_app (pullback.condition (f := f₁) (g := f₂)) X) x

/-- The comparison of fibre products used for condition (2): a section of `F(X₀) ×_{*} F(X₀)`
over `(U, s)` gives a section of `F(forgetSR X₀) ×_G F(forgetSR X₀)` over `U`. -/
def pullbackSecForget {X₀ : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)}
    (a : (associatedPresheafFunctor.{v}).obj X₀ ⟶
      liftedPresheaf.{v, w} (⊤_ ((CostructuredArrow (yoneda (C := C)) G)ᵒᵖ ⥤ Type v)))
    (Z : CostructuredArrow (yoneda (C := C)) G) (q : (pullback a a).obj (op Z)) :
    (pullback (augmentationOf G X₀) (augmentationOf G X₀)).obj (op Z.left) :=
  (pullback_app_exists (augmentationOf G X₀) (augmentationOf G X₀)
    (secForget G X₀ Z ((pullback.fst a a).app _ q)) (secForget G X₀ Z ((pullback.snd a a).app _ q))
    ((augmentationOf_secForget G X₀ Z _).trans (augmentationOf_secForget G X₀ Z _).symm)).choose

omit [HasPullbacks C] in
/-- The first projection of `pullbackSecForget a Z q` is `secForget` of the first projection
of `q`. -/
lemma pullbackSecForget_fst {X₀ : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)}
    (a : (associatedPresheafFunctor.{v}).obj X₀ ⟶
      liftedPresheaf.{v, w} (⊤_ ((CostructuredArrow (yoneda (C := C)) G)ᵒᵖ ⥤ Type v)))
    (Z : CostructuredArrow (yoneda (C := C)) G) (q : (pullback a a).obj (op Z)) :
    (pullback.fst (augmentationOf G X₀) (augmentationOf G X₀)).app (op Z.left)
        (pullbackSecForget a Z q) =
      secForget G X₀ Z ((pullback.fst a a).app _ q) :=
  (pullback_app_exists (augmentationOf G X₀) (augmentationOf G X₀) _ _
    ((augmentationOf_secForget G X₀ Z _).trans (augmentationOf_secForget G X₀ Z _).symm)
    ).choose_spec.1

omit [HasPullbacks C] in
/-- The second projection of `pullbackSecForget a Z q` is `secForget` of the second projection
of `q`. -/
lemma pullbackSecForget_snd {X₀ : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)}
    (a : (associatedPresheafFunctor.{v}).obj X₀ ⟶
      liftedPresheaf.{v, w} (⊤_ ((CostructuredArrow (yoneda (C := C)) G)ᵒᵖ ⥤ Type v)))
    (Z : CostructuredArrow (yoneda (C := C)) G) (q : (pullback a a).obj (op Z)) :
    (pullback.snd (augmentationOf G X₀) (augmentationOf G X₀)).app (op Z.left)
        (pullbackSecForget a Z q) =
      secForget G X₀ Z ((pullback.snd a a).app _ q) :=
  (pullback_app_exists (augmentationOf G X₀) (augmentationOf G X₀) _ _
    ((augmentationOf_secForget G X₀ Z _).trans (augmentationOf_secForget G X₀ Z _).symm)
    ).choose_spec.2

omit [HasPullbacks C] in
/-- `pullbackSecForget` commutes with restriction along a morphism `Z' ⟶ Z` of `C/G`. -/
lemma pullbackSecForget_restrict
    {X₀ : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)}
    (a : (associatedPresheafFunctor.{v}).obj X₀ ⟶
      liftedPresheaf.{v, w} (⊤_ ((CostructuredArrow (yoneda (C := C)) G)ᵒᵖ ⥤ Type v)))
    {Z Z' : CostructuredArrow (yoneda (C := C)) G} (f : Z' ⟶ Z) (q : (pullback a a).obj (op Z)) :
    pullbackSecForget a Z' ((pullback a a).map f.op q) =
      (pullback (augmentationOf G X₀) (augmentationOf G X₀)).map f.left.op
        (pullbackSecForget a Z q) := by
  apply pullback_app_ext (augmentationOf G X₀) (augmentationOf G X₀)
  all_goals simp only [pullbackSecForget_fst, pullbackSecForget_snd, NatTrans.naturality_apply,
    secForget_restrict]

omit [HasPullbacks C] in
/-- `pullbackSecForget` intertwines the maps `F(X₁) ⟶ F(X₀) × F(X₀)` over `C/G` and
`F(X₁) ⟶ F(X₀) ×_G F(X₀)` over `C` induced by `d₀` and `d₁`. -/
lemma pullbackSecForget_lift
    {X₀ X₁ : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)} (d₀ d₁ : X₁ ⟶ X₀)
    (a : (associatedPresheafFunctor.{v}).obj X₀ ⟶
      liftedPresheaf.{v, w} (⊤_ ((CostructuredArrow (yoneda (C := C)) G)ᵒᵖ ⥤ Type v)))
    (h' : (associatedPresheafFunctor.{v}).map d₀ ≫ a = (associatedPresheafFunctor.{v}).map d₁ ≫ a)
    (h : (associatedPresheafFunctor.{v}).map ((forgetSR G).map d₀) ≫ augmentationOf G X₀ =
      (associatedPresheafFunctor.{v}).map ((forgetSR G).map d₁) ≫ augmentationOf G X₀)
    (Z : CostructuredArrow (yoneda (C := C)) G)
    (p : ((associatedPresheafFunctor.{v}).obj X₁).obj (op Z)) :
    (pullback.lift ((associatedPresheafFunctor.{v}).map ((forgetSR G).map d₀))
        ((associatedPresheafFunctor.{v}).map ((forgetSR G).map d₁)) h).app _ (secForget G X₁ Z p) =
      pullbackSecForget a Z ((pullback.lift ((associatedPresheafFunctor.{v}).map d₀)
        ((associatedPresheafFunctor.{v}).map d₁) h').app _ p) := by
  apply pullback_app_ext (augmentationOf G X₀) (augmentationOf G X₀)
  all_goals simp only [pullback_lift_fst_app, pullback_lift_snd_app, pullbackSecForget_fst,
    pullbackSecForget_snd, secForget_map]

include hJ' in
/-- **Condition (2) of Stacks 09VU.** For two morphisms `d₀ d₁ : X₁ ⟶ X₀` of `SR(C/G)`, the map
`F(X₁) ⟶ F(X₀) × F(X₀)` over the final presheaf of `C/G` is locally surjective exactly when the
map `F(X₁) ⟶ F(X₀) ×_G F(X₀)` of the underlying objects of `SR(C)` is. -/
theorem isLocallySurjective_pullbackLift_iff
    {X₀ X₁ : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)} (d₀ d₁ : X₁ ⟶ X₀)
    (a : (associatedPresheafFunctor.{v}).obj X₀ ⟶
      liftedPresheaf.{v, w} (⊤_ ((CostructuredArrow (yoneda (C := C)) G)ᵒᵖ ⥤ Type v)))
    (h' : (associatedPresheafFunctor.{v}).map d₀ ≫ a = (associatedPresheafFunctor.{v}).map d₁ ≫ a)
    (h : (associatedPresheafFunctor.{v}).map ((forgetSR G).map d₀) ≫ augmentationOf G X₀ =
      (associatedPresheafFunctor.{v}).map ((forgetSR G).map d₁) ≫ augmentationOf G X₀) :
    Presheaf.IsLocallySurjective J'.toGrothendieck
        (pullback.lift ((associatedPresheafFunctor.{v}).map d₀)
          ((associatedPresheafFunctor.{v}).map d₁) h') ↔
      Presheaf.IsLocallySurjective J.toGrothendieck
        (pullback.lift ((associatedPresheafFunctor.{v}).map ((forgetSR G).map d₀))
          ((associatedPresheafFunctor.{v}).map ((forgetSR G).map d₁)) h) := by
  refine isLocallySurjective_iff_of_sections J.toGrothendieck J'.toGrothendieck
    (mem_toGrothendieck_iff J J' hJ') _ _ (secForget G X₁) (pullbackSecForget a)
    (fun f q ↦ pullbackSecForget_restrict a f q) (pullbackSecForget_lift d₀ d₁ a h' h) ?_ ?_
  · intro U q
    obtain ⟨s₀, e₁⟩ := exists_augmentationOf_eq_up G X₀ ((pullback.fst (augmentationOf G X₀)
      (augmentationOf G X₀)).app _ q)
    refine ⟨s₀, ?_⟩
    obtain ⟨z₁, hz₁⟩ := secForget_surjective G X₀ (.mk s₀) _ e₁
    obtain ⟨z₂, hz₂⟩ := secForget_surjective G X₀ (.mk s₀) _
      ((pullback_condition_app (augmentationOf G X₀) (augmentationOf G X₀) _ q).symm.trans e₁)
    obtain ⟨q', hq₁, hq₂⟩ := pullback_app_exists a a z₁ z₂
      ((subsingleton_liftedTerminal.{w} _).elim _ _)
    refine ⟨q', pullback_app_ext (augmentationOf G X₀) (augmentationOf G X₀) ?_ ?_⟩
    · exact (pullbackSecForget_fst a _ q').trans ((congrArg _ hq₁).trans hz₁)
    · exact (pullbackSecForget_snd a _ q').trans ((congrArg _ hq₂).trans hz₂)
  · intro Z p q hp
    have hfst := congrArg (fun x ↦ (pullback.fst (augmentationOf G X₀)
      (augmentationOf G X₀)).app _ x) hp
    have hsnd := congrArg (fun x ↦ (pullback.snd (augmentationOf G X₀)
      (augmentationOf G X₀)).app _ x) hp
    simp only at hfst hsnd
    rw [pullback_lift_fst_app, pullbackSecForget_fst] at hfst
    rw [pullback_lift_snd_app, pullbackSecForget_snd] at hsnd
    obtain ⟨z, rfl⟩ := secForget_surjective G X₁ Z p (augmentationOf_eq_of_map_eq G d₀ Z p _ hfst)
    refine ⟨z, pullback_app_ext a a ?_ ?_⟩ <;> apply secForget_injective G X₀ Z
    · rwa [pullback_lift_fst_app, secForget_map]
    · rwa [pullback_lift_snd_app, secForget_map]

end Conditions


/-! ### Coskeleta and functors preserving their limits -/

section Coskeleton

open SimplicialObject

/-- **A functor preserving the limits that define `cosk_n` commutes with `cosk_n`, compatibly
with the unit of the coskeleton adjunction.** The comparison is the canonical isomorphism of
right Kan extensions `Functor.rightKanExtensionCompIsoOfPreserves`. -/
theorem exists_coskAdj_unit_comp_eq {A B : Type*} [Category A] [Category B] (Φ : A ⥤ B) (n : ℕ)
    [∀ F : SimplicialObject.Truncated A n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    [∀ F : SimplicialObject.Truncated B n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    [∀ (F : SimplicialObject.Truncated A n) (c : SimplexCategoryᵒᵖ),
      PreservesLimit (StructuredArrow.proj c (SimplexCategory.Truncated.inclusion n).op ⋙ F) Φ]
    (K : SimplicialObject A) :
    ∃ e : (cosk n).obj K ⋙ Φ ≅ (cosk n).obj (K ⋙ Φ),
      Functor.whiskerRight ((coskAdj n).unit.app K) Φ ≫ e.hom = (coskAdj n).unit.app (K ⋙ Φ) := by
  refine ⟨Φ.rightKanExtensionCompIsoOfPreserves
    ((SimplexCategory.Truncated.inclusion n).op ⋙ K) (SimplexCategory.Truncated.inclusion n).op,
    ?_⟩
  apply Functor.hom_ext_of_isRightKanExtension _
    ((SimplexCategory.Truncated.inclusion n).op.ranCounit.app
      ((SimplexCategory.Truncated.inclusion n).op ⋙ K ⋙ Φ))
  ext a
  have h₁ := Functor.rightKanExtensionCompIsoOfPreserves_hom_fac_app Φ
    ((SimplexCategory.Truncated.inclusion n).op ⋙ K) (SimplexCategory.Truncated.inclusion n).op a
  have h₂ := Functor.ranCounit_app_app_ranAdjunction_unit_app_app
    (SimplexCategory.Truncated.inclusion n).op (H := A) K a
  have h₃ := Functor.ranCounit_app_app_ranAdjunction_unit_app_app
    (SimplexCategory.Truncated.inclusion n).op (H := B) (K ⋙ Φ) a
  refine Eq.trans ?_ h₃.symm
  refine (Category.assoc (Φ.map ((((SimplexCategory.Truncated.inclusion n).op.ranAdjunction
    A).unit.app K).app ((SimplexCategory.Truncated.inclusion n).op.obj a))) _ _).trans ?_
  refine (congrArg (fun m ↦ Φ.map ((((SimplexCategory.Truncated.inclusion n).op.ranAdjunction
    A).unit.app K).app ((SimplexCategory.Truncated.inclusion n).op.obj a)) ≫ m) h₁).trans ?_
  refine (Φ.map_comp _ _).symm.trans ?_
  exact (congrArg Φ.map h₂).trans (Φ.map_id _)

end Coskeleton


/-! ### The correspondence -/

section Hypercoverings

variable (G)

/-- The augmentation `F(K) ⟶ G` of the underlying simplicial object of `SR(C)` of a simplicial
object `K` of `SR(C/G)`. -/
def simplicialAugmentation
    (K : SimplicialObject (FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G))) :
    associatedSimplicialPresheaf.{v} (K ⋙ forgetSR G) ⟶
      (SimplicialObject.const _).obj (liftedPresheaf.{v, w} G) where
  app m := augmentationOf G (K.obj m)
  naturality m m' f := by
    change (associatedPresheafFunctor.{v}).map ((forgetSR G).map (K.map f)) ≫
      augmentationOf G (K.obj m') = augmentationOf G (K.obj m) ≫ 𝟙 _
    rw [map_comp_augmentationOf, Category.comp_id]

/-- The augmentation of `ofOver Y` is the given map `Y.hom`. -/
lemma augmentationOf_ofOver_obj
    (Y : CostructuredArrow (associatedPresheafFunctor.{v} (C := C)) (liftedPresheaf.{v, w} G)) :
    augmentationOf G ((ofOver G).obj Y) = Y.hom :=
  hom_ext_of_elementOf (fun i ↦
    (elementOf_augmentationOf G ((ofOver G).obj Y) i).trans
      (Equiv.apply_symm_apply yonedaEquiv (elementOf Y.hom i)))

/-- The simplicial object of `SR(C/G)` attached to a simplicial object of `SR(C)` augmented
towards `G`. -/
def liftSimplicial (K : SimplicialObject (FormalCoproduct.{w} C))
    (a : associatedSimplicialPresheaf.{v} K ⟶
      (SimplicialObject.const _).obj (liftedPresheaf.{v, w} G)) :
    SimplicialObject (FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)) :=
  K.toCostructuredArrow associatedPresheafFunctor.{v} (liftedPresheaf.{v, w} G) (fun m ↦ a.app m)
    (fun {_ _} f ↦ (a.naturality f).trans (Category.comp_id _)) ⋙ ofOver G

/-- The underlying simplicial object of `SR(C)` of `liftSimplicial G K a` is `K`. -/
lemma liftSimplicial_comp_forgetSR (K : SimplicialObject (FormalCoproduct.{w} C))
    (a : associatedSimplicialPresheaf.{v} K ⟶
      (SimplicialObject.const _).obj (liftedPresheaf.{v, w} G)) :
    liftSimplicial G K a ⋙ forgetSR G = K :=
  rfl

/-- The augmentation of `liftSimplicial G K a` towards `G` is `a`. -/
lemma simplicialAugmentation_liftSimplicial (K : SimplicialObject (FormalCoproduct.{w} C))
    (a : associatedSimplicialPresheaf.{v} K ⟶
      (SimplicialObject.const _).obj (liftedPresheaf.{v, w} G)) :
    simplicialAugmentation G (liftSimplicial G K a) = a :=
  NatTrans.ext (funext fun m ↦ augmentationOf_ofOver_obj G (CostructuredArrow.mk (a.app m)))

/-- Going from `SR(C/G)` to `SR(C)/G` and back is the identity, on the nose. -/
lemma toOver_comp_ofOver :
    toOver G ⋙ ofOver G = 𝟭 (FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)) := by
  have hobj : ∀ X : FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G),
      (ofOver G).obj ((toOver G).obj X) = X := by
    rintro ⟨I, obj⟩
    show (⟨I, fun i ↦ CostructuredArrow.mk (yonedaEquiv.symm
      (elementOf (augmentationOf G ⟨I, obj⟩) i))⟩ : FormalCoproduct _) = ⟨I, obj⟩
    congr 1
    funext i
    exact congrArg CostructuredArrow.mk ((congrArg yonedaEquiv.symm
      (elementOf_augmentationOf G ⟨I, obj⟩ i)).trans (yonedaEquiv.symm_apply_apply _))
  refine CategoryTheory.Functor.ext hobj (fun X Y f ↦ ?_)
  apply (forgetSR G).map_injective
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  show (forgetSR G).map f =
    eqToHom (rfl : (forgetSR G).obj X = _) ≫ (forgetSR G).map f ≫ eqToHom rfl
  simp

/-- A simplicial object `K` of `SR(C/G)` is recovered from its underlying simplicial object of
`SR(C)` and its augmentation towards `G`. -/
lemma liftSimplicial_simplicialAugmentation
    (K : SimplicialObject (FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G))) :
    liftSimplicial G (K ⋙ forgetSR G) (simplicialAugmentation G K) = K :=
  (congrArg (K ⋙ ·) (toOver_comp_ofOver G)).trans K.comp_id

/-- The augmentation of a simplicial object of `SR(C/G)` towards the final presheaf of `C/G`. -/
def terminalAugmentation
    (K : SimplicialObject (FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G))) :
    associatedSimplicialPresheaf.{v} K ⟶ (SimplicialObject.const _).obj
      (liftedPresheaf.{v, w} (⊤_ ((CostructuredArrow (yoneda (C := C)) G)ᵒᵖ ⥤ Type v))) where
  app _ := isTerminal_liftedTerminal.{w}.from _
  naturality _ _ _ := isTerminal_liftedTerminal.{w}.hom_ext _ _

/-- There is at most one morphism from a simplicial presheaf on `C/G` to the constant simplicial
object on the final presheaf. -/
instance subsingleton_hom_const_liftedTerminal
    (P : SimplicialObject ((CostructuredArrow (yoneda (C := C)) G)ᵒᵖ ⥤ Type (max v w))) :
    Subsingleton (P ⟶ (SimplicialObject.const _).obj
      (liftedPresheaf.{v, w} (⊤_ ((CostructuredArrow (yoneda (C := C)) G)ᵒᵖ ⥤ Type v)))) :=
  ⟨fun _ _ ↦ NatTrans.ext (funext fun _ ↦ isTerminal_liftedTerminal.{w}.hom_ext _ _)⟩

variable [HasPullbacks C] [HasEqualizers C] (J : Pretopology C)
  (J' : Pretopology (CostructuredArrow (yoneda (C := C)) G))
  (hJ' : J'.toGrothendieck =
    (CostructuredArrow.proj yoneda G).restrictedTopology J.toGrothendieck)

include hJ' in
/-- **Condition (3) of Stacks 09VU.** The higher matching maps of a simplicial object `K` of
`SR(C/G)` are locally surjective exactly when those of the underlying simplicial object of
`SR(C)` are: `forgetSR` preserves the positive coskeleta, compatibly with their units. -/
theorem isLocallySurjective_higherMatchingMap_iff
    (K : SimplicialObject (FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)))
    (n : ℕ) (hn : 1 ≤ n) :
    Presheaf.IsLocallySurjective J'.toGrothendieck (higherMatchingMap.{v} K n hn) ↔
      Presheaf.IsLocallySurjective J.toGrothendieck
        (higherMatchingMap.{v} (K ⋙ forgetSR G) n hn) := by
  let := hasPositiveCoskeleta.{w} (C := CostructuredArrow (yoneda (C := C)) G) n hn
  let := hasPositiveCoskeleta.{w} (C := C) n hn
  have : NeZero n := ⟨by omega⟩
  have hconn : ∀ c : SimplexCategoryᵒᵖ,
      IsConnected (StructuredArrow c (SimplexCategory.Truncated.inclusion n).op) :=
    fun c ↦ Functor.Final.out c
  obtain ⟨e, he⟩ := exists_coskAdj_unit_comp_eq (forgetSR.{w} G) n K
  rw [higherMatchingMap_eq, higherMatchingMap_eq, isLocallySurjective_map_iff J J' hJ']
  have h := congr_app he (op ⦋n + 1⦌)
  rw [NatTrans.comp_app, Functor.whiskerRight_app] at h
  rw [← h, Functor.map_comp, Presheaf.isLocallySurjective_comp_iff]

omit [HasEqualizers C] in
include hJ' in
/-- **Condition (1) of Stacks 09VU**, for a simplicial object of `SR(C/G)`. -/
theorem isLocallySurjective_augmentation_zero_iff
    (K : SimplicialObject (FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)))
    (a : associatedSimplicialPresheaf.{v} K ⟶ (SimplicialObject.const _).obj
      (liftedPresheaf.{v, w} (⊤_ ((CostructuredArrow (yoneda (C := C)) G)ᵒᵖ ⥤ Type v)))) :
    Presheaf.IsLocallySurjective J'.toGrothendieck (a.app (op ⦋0⦌)) ↔
      Presheaf.IsLocallySurjective J.toGrothendieck
        ((simplicialAugmentation G K).app (op ⦋0⦌)) :=
  isLocallySurjective_toTerminal_iff J J' hJ' _ _

omit [HasEqualizers C] in
include hJ' in
/-- **Condition (2) of Stacks 09VU**, for a simplicial object of `SR(C/G)`. -/
theorem isLocallySurjective_oneMatchingMap_iff
    (K : SimplicialObject (FormalCoproduct.{w} (CostructuredArrow (yoneda (C := C)) G)))
    (a : associatedSimplicialPresheaf.{v} K ⟶ (SimplicialObject.const _).obj
      (liftedPresheaf.{v, w} (⊤_ ((CostructuredArrow (yoneda (C := C)) G)ᵒᵖ ⥤ Type v)))) :
    Presheaf.IsLocallySurjective J'.toGrothendieck
        (oneMatchingMap (associatedSimplicialPresheaf.{v} K) _ a) ↔
      Presheaf.IsLocallySurjective J.toGrothendieck
        (oneMatchingMap (associatedSimplicialPresheaf.{v} (K ⋙ forgetSR G)) _
          (simplicialAugmentation G K)) :=
  isLocallySurjective_pullbackLift_iff J J' hJ' (K.δ 0) (K.δ 1) (a.app (op ⦋0⦌)) _ _

include hJ' in
/-- A hypercovering of the site `C/G` gives a hypercovering of `G`: forget the elements. -/
def toHypercoveringOf (H : HypercoveringOfTerminal.{w} J') : HypercoveringOf.{v, w} J G where
  toSimplicialObject := H.toSimplicialObject ⋙ forgetSR G
  augmentation := simplicialAugmentation G H.toSimplicialObject
  locallySurjective_zero :=
    (isLocallySurjective_augmentation_zero_iff G J J' hJ' _ _).1 H.locallySurjective_zero
  locallySurjective_one :=
    (isLocallySurjective_oneMatchingMap_iff G J J' hJ' _ _).1 H.locallySurjective_one
  locallySurjective_succ n hn :=
    (isLocallySurjective_higherMatchingMap_iff G J J' hJ' _ n hn).1
      (H.locallySurjective_succ n hn)

include hJ' in
/-- A hypercovering of `G` gives a hypercovering of the site `C/G`: a map `F(K_n) ⟶ G` is a
family of elements of `G` over the summands of `K_n`. -/
def ofHypercoveringOf (H : HypercoveringOf.{v, w} J G) : HypercoveringOfTerminal.{w} J' where
  toSimplicialObject := liftSimplicial G H.toSimplicialObject H.augmentation
  augmentation := terminalAugmentation G _
  locallySurjective_zero := by
    refine (isLocallySurjective_augmentation_zero_iff G J J' hJ' _ _).2 ?_
    rw [simplicialAugmentation_liftSimplicial]
    exact H.locallySurjective_zero
  locallySurjective_one := by
    refine (isLocallySurjective_oneMatchingMap_iff G J J' hJ' _ _).2 ?_
    rw [simplicialAugmentation_liftSimplicial]
    exact H.locallySurjective_one
  locallySurjective_succ n hn :=
    (isLocallySurjective_higherMatchingMap_iff G J J' hJ' _ n hn).2
      (H.locallySurjective_succ n hn)

include hJ' in
/-- **Hypercoverings of `G` are hypercoverings of the site `C/G`**, as an equivalence of types:
the two constructions `toHypercoveringOf` and `ofHypercoveringOf` are mutually inverse. -/
def hypercoveringEquiv : HypercoveringOf.{v, w} J G ≃ HypercoveringOfTerminal.{w} J' where
  toFun := ofHypercoveringOf G J J' hJ'
  invFun := toHypercoveringOf G J J' hJ'
  left_inv H := by
    refine HypercoveringOf.ext rfl (heq_of_eq ?_)
    exact simplicialAugmentation_liftSimplicial G H.toSimplicialObject H.augmentation
  right_inv H := by
    have hK : liftSimplicial G (H.toSimplicialObject ⋙ forgetSR G)
        (simplicialAugmentation G H.toSimplicialObject) = H.toSimplicialObject :=
      liftSimplicial_simplicialAugmentation G H.toSimplicialObject
    exact HypercoveringOf.ext hK (Subsingleton.helim
      (congrArg (fun K ↦ associatedSimplicialPresheaf.{v} K ⟶ (SimplicialObject.const _).obj
        (liftedPresheaf.{v, w} (⊤_ ((CostructuredArrow (yoneda (C := C)) G)ᵒᵖ ⥤ Type v)))) hK) _ _)

end Hypercoverings


/-! ### The localized site -/

section LocalizationPretopology

variable [HasPullbacks C] [HasEqualizers C] (J : Pretopology C) (G)

/-- The pretopology on the localization `C/G` of Stacks 0791: a family of morphisms into `(U, s)`
is covering when the sieve it generates covers, i.e. when its image in `C` generates a covering
sieve of `U`. -/
def localizationPretopology : Pretopology (CostructuredArrow (yoneda (C := C)) G) :=
  ((CostructuredArrow.proj yoneda G).restrictedTopology J.toGrothendieck).toPretopology

omit [HasEqualizers C] in
/-- The Grothendieck topology generated by `localizationPretopology G J` is the topology on `C/G`
restricted from `J` along `CostructuredArrow.proj yoneda G`. -/
lemma localizationPretopology_toGrothendieck :
    (localizationPretopology G J).toGrothendieck =
      (CostructuredArrow.proj yoneda G).restrictedTopology J.toGrothendieck :=
  (Pretopology.gi _).l_u_eq _

/-- **A hypercovering of `G` is the same thing as a hypercovering of the site `C/G`.** Let `C` be a
site, given by a pretopology `J`, with equalizers and fibre products, and let `G` be a presheaf of
sets on `C`. Hypercoverings of `G` in `C` (Stacks 09VU) correspond bijectively to hypercoverings of
the localized site `C/G` of Stacks 0791: a hypercovering `K` of `G` goes to the simplicial object
`n ↦ {(K_{n,i}, s_{n,i})}` of `SR(C/G)`, where `s_{n,i}` is the restriction of the augmentation
`F(K_n) ⟶ G` to the summand `h_{K_{n,i}}`, and the three conditions of Stacks 09VU for `K` over `G`
are the three conditions for it over the final presheaf of `C/G`. -/
@[stacks 09X6 "a hypercovering of `G` in `C` is the same thing as a hypercovering for the site
  `C/G`, for the site `C/G` of Stacks 0791 (coverings: families whose image generates a covering
  sieve of `C`)"]
def hypercoveringOfEquivLocalization :
    HypercoveringOf.{v, w} J G ≃ HypercoveringOfTerminal.{w} (localizationPretopology G J) :=
  hypercoveringEquiv G J (localizationPretopology G J) (localizationPretopology_toGrothendieck G J)

/-- The hypercovering of `C/G` attached to a hypercovering `K` of `G` has underlying simplicial
object of `SR(C)` the simplicial object `K` itself, on the nose. -/
lemma hypercoveringOfEquivLocalization_toSimplicialObject (H : HypercoveringOf.{v, w} J G) :
    (hypercoveringOfEquivLocalization G J H).toSimplicialObject ⋙ forgetSR G =
      H.toSimplicialObject :=
  rfl

end LocalizationPretopology

end Stacks.CategoryTheory.Hypercovering.LocalizationAtPresheaf

end
