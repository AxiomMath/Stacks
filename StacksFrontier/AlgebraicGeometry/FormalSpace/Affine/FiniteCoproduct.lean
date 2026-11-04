module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Fubini
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticColimit
public import StacksFrontier.AlgebraicGeometry.Morphisms.SigmaMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.AffineFiniteCoproducts
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# A finite coproduct of affine formal algebraic spaces is an affine formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `Z i` be affine formal algebraic
spaces over `S` indexed by a finite type `I`. Each `Z i` is, by Stacks 0AI7, the colimit of a
nonempty directed diagram `D i : Idx i ⥤ BigAffineFppf` of affine schemes over `S` whose
transition morphisms are thickenings. The coproduct `∐ Z` is presented by the *product* of the
index preorders: over `Λ = ∏ᵢ Idx i`, ordered pointwise, the diagram `λ ↦ ∐ᵢ (D i) (λ i)` is a
nonempty directed diagram of affine schemes over `S` — the big affine fppf category over `S` has
finite coproducts, by Stacks 021S — whose transition morphisms are thickenings, and whose colimit
is `∐ Z`.

Two facts make the last clause work. First, the sheafified Yoneda embedding of the big fppf site
of `S` preserves finite coproducts, because the site is subcanonical and its finite coproducts
are disjoint coverings; so a coproduct of stages inside the site becomes the coproduct of their
sheaves. Second, the projection `Λ ⥤ Idx i` is a final functor — `Λ` is directed and every object
of `Idx i` is a coordinate of some point of `Λ` — so a colimit over `Λ` of a diagram pulled back
along the projection is the colimit over `Idx i`; interchanging the finite coproduct with the
colimit over `Λ` by Fubini then gives `colim_Λ ∐ᵢ (D i)(λ i) ≅ ∐ᵢ colim_{Idx i} (D i)`.

The set-theoretic condition of Stacks 0AIS for `∐ Z` is not proved again from scratch: the
coproduct `∐ᵢ U i` of objects of the site representing surjections onto the `Z i` is an object of
the site, its sheaf is `∐ᵢ h_{U i}^#`, and the induced map onto `∐ Z` is a surjection out of a
representable, which is exactly the hypothesis of
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_colimit_of_representable_epi`.

## Main results

* `Stacks.Thickenings.isThickening_sigmaMap`: a finite coproduct of thickenings of schemes is a
  thickening.
* `AlgebraicGeometry.FormalSpace.sigmaColimitIso`: the interchange of a finite coproduct with the
  directed colimits presenting its summands.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_sigma_of_presentations`: **a
  coproduct of finitely many affine formal algebraic spaces over `S`, each given with a
  presentation, is an affine formal algebraic space over `S`.** Choosing the presentations gives
  `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_sigma`, the step of Stacks 0AJ9
  which passes from condition (2) to condition (3).

## Implementation notes

`AlgebraicGeometry.FormalSpace.StageIndex` wraps the product `∀ i, Idx i` of the index preorders
in a one-field structure rather than using the product type itself. The wrapper is not cosmetic:
on a bare product of types carrying categories Lean's instance resolution prefers the product
*category* structure `CategoryTheory.pi` to the one coming from the product order, and Stacks
0AI7 asks for a diagram over the order; and a type synonym, which would fix that, leaves the
projections to the factors type-incorrect at the transparency `rewrite` checks its motives at.
The structure carries the order instances only, so the category structure on it is unambiguously
the one of `CategoryTheory.Preorder.smallCategory`.

The index type of the coproduct lives in `Type (u + 1)`, as it does in Definition 0AIM; finite
coproducts in the site are available at every universe because a finite type is small.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Thickenings

/-- **A finite coproduct of thickenings of schemes is a thickening.** Both halves of the
condition — being a closed immersion and being surjective on points — are Zariski local at the
target, and a property local at the target is stable under finite disjoint unions by
`AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap`. -/
theorem isThickening_sigmaMap {ι : Type v} [Finite ι] {X Y : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, IsThickening (f i)) :
    IsThickening (Limits.Sigma.map f) := by
  refine ⟨IsZariskiLocalAtTarget.sigmaMap f fun i ↦ (hf i).1, ?_⟩
  exact (IsZariskiLocalAtTarget.sigmaMap (P := @Surjective) f fun i ↦ ⟨(hf i).2⟩).surj

/-- A thickening stays a thickening after composing with isomorphisms on either side. -/
theorem isThickening_isoComp {W X Y Z : Scheme.{u}} (a : W ≅ X) {f : X ⟶ Y} (b : Y ≅ Z)
    (hf : IsThickening f) : IsThickening (a.hom ≫ f ≫ b.hom) := by
  have : IsClosedImmersion f := hf.1
  have : Surjective f := ⟨hf.2⟩
  exact ⟨inferInstance, Scheme.Hom.surjective _⟩

end Stacks.Thickenings

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The sheafified Yoneda embedding preserves finite coproducts -/

/-- The Yoneda embedding of the big fppf site of `S` into sheaves of `Type (u + 1)` preserves
finite coproducts: a coproduct of a finite family of objects of the site is computed on
underlying schemes, and `AlgebraicGeometry.BigFppfOver.isColimitUliftYonedaCofan` turns such a
coproduct of schemes into a coproduct of representable sheaves. -/
instance preservesColimitsOfShape_discrete_uliftYoneda (ι : Type v) [Finite ι] :
    PreservesColimitsOfShape (Discrete ι)
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}) := by
  have : Small.{u} ι := inferInstance
  apply (config := { allowSynthFailures := true }) preservesColimitsOfShape_of_discrete
  refine fun X ↦ ⟨fun {c : Cofan X} hc ↦ ⟨(Cofan.isColimitMapCoconeEquiv _ _ _).symm ?_⟩⟩
  exact BigFppfOver.isColimitUliftYonedaCofan B S hS X c.inj
    (Cofan.isColimitMapCoconeEquiv (BigFppfOver.toScheme B S hS) X c
      (isColimitOfPreserves (BigFppfOver.toScheme B S hS) hc))

/-- The sheafified Yoneda embedding of the big fppf site of `S` preserves finite coproducts: the
topology is subcanonical, so it agrees with the Yoneda embedding into sheaves. -/
instance preservesColimitsOfShape_discrete_sheafifiedYoneda (ι : Type v) [Finite ι] :
    PreservesColimitsOfShape (Discrete ι)
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) :=
  preservesColimitsOfShape_of_natIso
    (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)).symm

/-- The functor sending an affine object of the big fppf site of `S` to the fppf sheaf it
represents: the sheafified Yoneda embedding restricted to the big affine fppf category. Its
nonempty directed colimits along thickenings are the affine formal algebraic spaces of
Stacks 0AI7. -/
abbrev affineStageSheafFunctor : BigAffineFppf B S hS ⥤ FppfSheaf B S hS :=
  BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)

/-- **The first half of the set-theoretic condition of Stacks 0AIS, as a surjection from a
sheafified representable.** The condition records representability of the source of the
surjection by an isomorphism of underlying presheaves with a universe-lifted Yoneda presheaf;
sheafifying that isomorphism identifies the source with the sheafified representable of the same
object of the site. -/
theorem exists_epi_sheafifiedYoneda_of_satisfiesSetTheoreticCondition {X : FppfSheaf B S hS}
    (hX : SatisfiesSetTheoreticCondition B S hS X) :
    ∃ (U : BigFppfOver B S hS)
      (f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X), Epi f := by
  obtain ⟨U, R, hU, hR, ⟨eU⟩, -, f, hf, -⟩ := hX
  have eiso : hU ≅ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U :=
    sheafificationIso hU ≪≫
      (presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso eU
  refine ⟨U, eiso.inv ≫ f, ?_⟩
  have : Epi (eiso.hom ≫ eiso.inv ≫ f) := by rw [Iso.hom_inv_id_assoc]; exact hf
  exact epi_of_epi eiso.hom _

/-! ### Coproducts of thickenings in the big affine fppf category -/

section SigmaMap

variable {ι : Type v} [Finite ι]

/-- The comparison isomorphism between the coproduct of the underlying schemes of a finite family
of affine objects of the big fppf site of `S` and the underlying scheme of their coproduct in the
big affine fppf category. -/
def toSchemeSigmaIso (W : ι → BigAffineFppf B S hS) :
    (∐ fun i ↦ (BigAffineFppf.toScheme B S hS).obj (W i)) ≅
      (BigAffineFppf.toScheme B S hS).obj (∐ W) :=
  (coproductIsCoproduct _).coconePointUniqueUpToIso
    (Cofan.isColimitMapCoconeEquiv (BigAffineFppf.toScheme B S hS) W _
      (isColimitOfPreserves (BigAffineFppf.toScheme B S hS) (coproductIsCoproduct W)))

/-- The comparison isomorphism `toSchemeSigmaIso` carries the `i`-th coprojection of the coproduct
of underlying schemes to the image under the functor to schemes of the `i`-th coprojection of the
coproduct in the big affine fppf category. -/
theorem sigmaι_toSchemeSigmaIso_hom (W : ι → BigAffineFppf B S hS) (i : ι) :
    Sigma.ι (fun i ↦ (BigAffineFppf.toScheme B S hS).obj (W i)) i ≫
        (toSchemeSigmaIso B S hS W).hom =
      (BigAffineFppf.toScheme B S hS).map (Sigma.ι W i) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk i)

/-- **A finite coproduct in the big affine fppf category over `S` of morphisms which are
thickenings on underlying schemes is a thickening on underlying schemes.** The functor to schemes
preserves finite coproducts, so the morphism of coproducts is, up to the comparison isomorphisms,
the coproduct of the morphisms of underlying schemes. -/
theorem isThickening_toScheme_map_sigmaMap {X Y : ι → BigAffineFppf B S hS} (p : ∀ i, X i ⟶ Y i)
    (hp : ∀ i, Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (p i))) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (Limits.Sigma.map p)) := by
  have key : (toSchemeSigmaIso B S hS X).hom ≫
      (BigAffineFppf.toScheme B S hS).map (Limits.Sigma.map p) =
      Limits.Sigma.map (fun i ↦ (BigAffineFppf.toScheme B S hS).map (p i)) ≫
        (toSchemeSigmaIso B S hS Y).hom := by
    refine Limits.Sigma.hom_ext _ _ fun i ↦ ?_
    rw [← Category.assoc, sigmaι_toSchemeSigmaIso_hom, ← Functor.map_comp, Limits.Sigma.ι_map,
      Functor.map_comp, ← Category.assoc, Limits.Sigma.ι_map, Category.assoc,
      sigmaι_toSchemeSigmaIso_hom]
  have heq : (BigAffineFppf.toScheme B S hS).map (Limits.Sigma.map p) =
      (toSchemeSigmaIso B S hS X).inv ≫
        Limits.Sigma.map (fun i ↦ (BigAffineFppf.toScheme B S hS).map (p i)) ≫
          (toSchemeSigmaIso B S hS Y).hom := by
    rw [← key, Iso.inv_hom_id_assoc]
  rw [heq]
  exact Stacks.Thickenings.isThickening_isoComp (toSchemeSigmaIso B S hS X).symm
    (toSchemeSigmaIso B S hS Y) (Stacks.Thickenings.isThickening_sigmaMap _ hp)

end SigmaMap

/-! ### The product of the index preorders -/

section StageIndex

variable {I : Type (u + 1)} (Idx : I → Type (u + 1)) [∀ i, Preorder (Idx i)]

/-- The index preorder of the presentation of a finite coproduct: the product `∏ᵢ Idx i` of the
index preorders of the presentations of the summands, ordered pointwise. -/
structure StageIndex where
  /-- The chosen stage in each factor. -/
  coord : ∀ i, Idx i

/-- The pointwise preorder on the product of the index preorders. -/
instance : Preorder (StageIndex Idx) where
  le lam mu := ∀ i, lam.coord i ≤ mu.coord i
  le_refl _ _ := le_refl _
  le_trans _ _ _ h₁ h₂ i := (h₁ i).trans (h₂ i)

/-- The product of nonempty index preorders is nonempty. -/
instance [∀ i, Nonempty (Idx i)] : Nonempty (StageIndex Idx) :=
  ⟨⟨fun i ↦ Classical.arbitrary (Idx i)⟩⟩

/-- Comparison in the product of the index preorders is comparison at every index. -/
theorem StageIndex.le_def {lam mu : StageIndex Idx} :
    lam ≤ mu ↔ ∀ i, lam.coord i ≤ mu.coord i := Iff.rfl

/-- The product of directed preorders is directed: an upper bound may be chosen at each index
separately. -/
instance isDirectedOrder_stageIndex [∀ i, IsDirectedOrder (Idx i)] :
    IsDirectedOrder (StageIndex Idx) where
  directed lam mu := by
    choose nu h₁ h₂ using fun i ↦ exists_ge_ge (lam.coord i) (mu.coord i)
    exact ⟨⟨nu⟩, h₁, h₂⟩

/-- The projection of the product of the index preorders onto its `i`-th factor. -/
def stageProj (i : I) : StageIndex Idx ⥤ Idx i :=
  Monotone.functor (f := fun lam : StageIndex Idx ↦ lam.coord i) fun _ _ h ↦ h i

/-- **The projection of the product of the index preorders onto a factor is final.** Every object
of `Idx i` is a coordinate of a point of the product, and the product is directed, so the fibres
of the projection are filtered. Consequently a colimit over the product of a diagram pulled back
along the projection is the colimit over `Idx i`. -/
instance final_stageProj [∀ i, Nonempty (Idx i)] [∀ i, IsDirectedOrder (Idx i)] (i : I) :
    (stageProj Idx i).Final := by
  classical
  apply Functor.final_of_exists_of_isFiltered
  · intro d
    refine ⟨⟨Function.update (fun j ↦ Classical.arbitrary (Idx j)) i d⟩, ⟨homOfLE ?_⟩⟩
    exact le_of_eq (Function.update_self i d (fun j ↦ Classical.arbitrary (Idx j))).symm
  · intro d c s s'
    exact ⟨c, 𝟙 c, Subsingleton.elim _ _⟩

end StageIndex

/-! ### The diagram of finite coproducts of stages -/

section Diagram

variable {I : Type (u + 1)} [Finite I] (Idx : I → Type (u + 1)) [∀ i, Preorder (Idx i)]
  (D : ∀ i, Idx i ⥤ BigAffineFppf B S hS)

/-- The diagram of families of stages: over a point `λ` of the product of the index preorders it
is the family `i ↦ (D i)(λ i)` of affine objects of the site, read as a diagram on `Discrete I`
so that its colimit is their coproduct. -/
def stageFamily : StageIndex Idx ⥤ (Discrete I ⥤ BigAffineFppf B S hS) where
  obj lam := Discrete.functor fun i ↦ (D i).obj (lam.coord i)
  map h := Discrete.natTrans fun i ↦ (D i.as).map (homOfLE (leOfHom h i.as))
  map_id lam := by
    refine NatTrans.ext (funext fun i ↦ ?_)
    obtain ⟨i⟩ := i
    exact (D i).map_id _
  map_comp f g := by
    refine NatTrans.ext (funext fun i ↦ ?_)
    obtain ⟨i⟩ := i
    exact (D i).map_comp _ _

/-- **The directed diagram of affine stages presenting a finite coproduct.** Over a point `λ` of
the product of the index preorders it is the coproduct `∐ᵢ (D i)(λ i)`, formed in the big affine
fppf category over `S`, which has finite coproducts by Stacks 021S. -/
def sigmaStage : StageIndex Idx ⥤ BigAffineFppf B S hS :=
  stageFamily B S hS Idx D ⋙ colim

/-- The transition morphism of the diagram of coproducts of stages is the coproduct of the
transition morphisms of the summands. -/
theorem sigmaStage_map {lam mu : StageIndex Idx} (h : lam ⟶ mu) :
    (sigmaStage B S hS Idx D).map h =
      Limits.Sigma.map (fun i ↦ (D i).map (homOfLE (leOfHom h i))) :=
  rfl

/-- **The transition morphisms of the diagram of coproducts of stages are thickenings**, being
coproducts of the thickenings of the summands. -/
theorem isThickening_sigmaStage_map
    (hD : ∀ i, ∀ ⦃a b : Idx i⦄ (f : a ⟶ b),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map ((D i).map f)))
    {lam mu : StageIndex Idx} (h : lam ⟶ mu) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map ((sigmaStage B S hS Idx D).map h)) :=
  isThickening_toScheme_map_sigmaMap B S hS
    (fun i ↦ (D i).map (homOfLE (leOfHom h i))) fun i ↦ hD i _

/-! ### The colimit of the diagram of coproducts of stages -/

/-- The diagram of families of sheaves of stages: the diagram of families of stages followed by
the sheaf of each member. -/
def stageFamilySheaf : StageIndex Idx ⥤ (Discrete I ⥤ FppfSheaf B S hS) :=
  stageFamily B S hS Idx D ⋙
    (Functor.whiskeringRight (Discrete I) (BigAffineFppf B S hS) (FppfSheaf B S hS)).obj
      (affineStageSheafFunctor B S hS)

/-- **Interchange of a finite coproduct with the directed colimits presenting its summands.** The
colimit, over the product of the index preorders, of the coproducts of the sheaves of the stages
is the coproduct of the colimits of the sheaves of the stages.

The colimit over the product and the finite coproduct are interchanged by Fubini
(`CategoryTheory.Limits.colimitFlipCompColimIsoColimitCompColim`), and the colimit over the
product of a diagram pulled back along the projection to the `i`-th factor is the colimit over
that factor because the projection is final. -/
def sigmaColimitIso [∀ i, Nonempty (Idx i)] [∀ i, IsDirectedOrder (Idx i)]
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)]
    (Z : I → FppfSheaf B S hS)
    (e : ∀ i, Z i ≅ colimit (D i ⋙ affineStageSheafFunctor B S hS)) :
    (∐ Z) ≅ colimit (sigmaStage B S hS Idx D ⋙ affineStageSheafFunctor B S hS) :=
  let α : Discrete.functor Z ≅ (stageFamilySheaf B S hS Idx D).flip ⋙ colim :=
    Discrete.natIso fun i ↦ e i.as ≪≫
      (Functor.Final.colimitIso (stageProj Idx i.as)
        (D i.as ⋙ affineStageSheafFunctor B S hS)).symm
  let β : stageFamilySheaf B S hS Idx D ⋙ colim ≅
      sigmaStage B S hS Idx D ⋙ affineStageSheafFunctor B S hS :=
    (Functor.isoWhiskerLeft (stageFamily B S hS Idx D)
      (preservesColimitNatIso (J := Discrete I) (affineStageSheafFunctor B S hS))).symm
  HasColimit.isoOfNatIso α ≪≫
    colimitFlipCompColimIsoColimitCompColim (stageFamilySheaf B S hS Idx D) ≪≫
      HasColimit.isoOfNatIso β

end Diagram

/-! ### The theorem -/

section Main

variable {I : Type (u + 1)} [Finite I] (Idx : I → Type (u + 1)) [∀ i, Preorder (Idx i)]
  [∀ i, Nonempty (Idx i)] [∀ i, IsDirectedOrder (Idx i)]
  (D : ∀ i, Idx i ⥤ BigAffineFppf B S hS)

/-- A coproduct of finitely many affine formal algebraic spaces over `S`, presentations of the
summands being given, is an affine formal algebraic space over `S`.

The presentation is the diagram of coproducts of stages over the product of the index preorders;
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_colimit_of_representable_epi`
supplies the set-theoretic condition of Stacks 0AIS from the surjection onto `∐ Z` out of the
sheaf of the coproduct of objects of the site representing surjections onto the summands. -/
theorem isAffineFormalAlgebraicSpace_sigma_of_presentations
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)]
    (hD : ∀ i, ∀ ⦃a b : Idx i⦄ (f : a ⟶ b),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map ((D i).map f)))
    (Z : I → FppfSheaf B S hS)
    (hZset : ∀ i, SatisfiesSetTheoreticCondition B S hS (Z i))
    (e : ∀ i, Z i ≅ colimit (D i ⋙ affineStageSheafFunctor B S hS)) :
    IsAffineFormalAlgebraicSpace B S hS (∐ Z) := by
  classical
  have pres : (∐ Z) ≅ colimit (sigmaStage B S hS Idx D ⋙ affineStageSheafFunctor B S hS) :=
    sigmaColimitIso B S hS Idx D Z e
  choose U fU hfU using fun i ↦
    exists_epi_sheafifiedYoneda_of_satisfiesSetTheoreticCondition B S hS (hZset i)
  have hVcol : IsColimit (Cofan.mk
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (∐ U))
      fun i ↦ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (Sigma.ι U i)) :=
    Cofan.isColimitMapCoconeEquiv (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) U _
      (isColimitOfPreserves (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
        (coproductIsCoproduct U))
  have eV : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (∐ U) ≅
      ∐ fun i ↦ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (U i) :=
    hVcol.coconePointUniqueUpToIso (coproductIsCoproduct _)
  exact ⟨satisfiesSetTheoreticCondition_of_colimit_of_representable_epi B S hS
      (sigmaStage B S hS Idx D)
      (fun _ _ f ↦ isThickening_sigmaStage_map B S hS Idx D hD f) (∐ Z) ⟨pres⟩ (∐ U)
      (eV.hom ≫ Limits.Sigma.map fU) (epi_comp _ _),
    StageIndex Idx, inferInstance, inferInstance, inferInstance, sigmaStage B S hS Idx D,
    fun _ _ f ↦ isThickening_sigmaStage_map B S hS Idx D hD f, ⟨pres⟩⟩

end Main

end AlgebraicGeometry.FormalSpace

end
