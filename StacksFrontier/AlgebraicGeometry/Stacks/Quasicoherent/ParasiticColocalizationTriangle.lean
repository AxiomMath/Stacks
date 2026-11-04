module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedFlatFppfRestriction

/-!
# Splitting off the parasitic part of a complex on an algebraic stack

Let `𝒳` be an algebraic stack and let `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` be the morphism of
ringed topoi of **Stacks 0788** (2).  **Stacks 07BA** says that every object `K` of
`D_{LQCoh^fbc}(𝒪_𝒳)` sits in a *canonical* distinguished triangle

`K' ⟶ K ⟶ P ⟶ K'[1]`

of `D_{LQCoh^fbc}(𝒪_𝒳)` whose third term `P` lies in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` and whose
first term `K'` satisfies `Hom_{D(𝒪_𝒳)}(K', P') = 0` for every `P'` in
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.  In other words `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` is a
*colocalizing*, i.e. left admissible, subcategory of `D_{LQCoh^fbc}(𝒪_𝒳)`: this is the
Bousfield colocalization underlying the Verdier quotient of **Stacks 07B6**.

The canonical data is not the cone but the pair

`K' = Lg_! g^* K`, `ε_K : K' ⟶ K` the counit of `Lg_! ⊣ g^*`,

and that is what is constructed below, as
`AlgebraicGeometry.Stack.FlatFppf.parasiticFreePart` and
`AlgebraicGeometry.Stack.FlatFppf.parasiticFreePartHom`.  The third term of the triangle is a
cone on `ε_K`, determined by the above only up to isomorphism, so the two properties of the
source are proved for *every* distinguished triangle extending `ε_K` rather than for one chosen
cone; see the implementation notes.

## Main definitions

* `AlgebraicGeometry.Stack.FlatFppf.parasiticFreePart`: the object `K' = Lg_! g^* K`.
* `AlgebraicGeometry.Stack.FlatFppf.parasiticFreePartHom`: the canonical morphism `K' ⟶ K`, the
  counit of the adjunction `Lg_! ⊣ g^*` at `K`.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.isIso_derivedModuleRestriction_map_parasiticFreePartHom`:
  `g^* ε_K` is an isomorphism, because `g^* Lg_! = id`.
* `AlgebraicGeometry.Stack.FlatFppf.leftOrthogonal_parasiticFreePart`: **Stacks 07BA**, the
  orthogonality — `Hom_{D(𝒪_𝒳)}(K', P') = 0` for every `P'` in
  `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.FlatFppf.derivedParasitic_obj₃_of_distTriang_parasiticFreePartHom`:
  **Stacks 07BA**, the cone — any cone on `ε_K` lies in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.FlatFppf.extensionProduct_parasiticFreePart`: **Stacks 07BA** in the
  shape the source states it — every `K` in `D_{LQCoh^fbc}(𝒪_𝒳)` is an extension of an object of
  `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` by an object of `D_{LQCoh^fbc}(𝒪_𝒳)` left orthogonal to it.

## Implementation notes

### What is data and what is not

The source calls the triangle canonical, and it is: by [Stacks, Tag 0CQP] a triangle on a fixed
morphism is unique up to an isomorphism of triangles which is the identity on the middle term, so
the canonical content is exactly the pair `(K', ε_K)`, which is a genuine construction with a
real body — the counit of `Lg_! ⊣ g^*` at `K`, no choice involved.

The third term cannot be produced as data: in Mathlib the existence of a cone is the
`Pretriangulated.distinguished_cocone_triangle` field of the `Pretriangulated` class, a
`Prop`-valued existential, so no cone functor is available on `D(𝒪_𝒳)` and any `def` producing
one would have to go through `Classical.choose`.  The two assertions of the source are therefore
stated here for an arbitrary distinguished triangle extending `ε_K`, which is strictly stronger
than picking one cone; `AlgebraicGeometry.Stack.FlatFppf.extensionProduct_parasiticFreePart`
packages those together with
`CategoryTheory.Pretriangulated.distinguished_cocone_triangle` into the existential statement of
the source.

### The hypotheses carried, and why

The source's proof uses `Lg_!` on the derived categories of *modules*, which is **Stacks 07AS**
part (4).  The library has **Stacks 07AS** part (3), for abelian sheaves
(`AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriekAdjunction` and
`AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriekRestrictionIso`), and the *underived*
module-level statement, **Stacks 0789** part (2)
(`AlgebraicGeometry.Stack.FlatFppf.moduleShriekAdjunction` and
`AlgebraicGeometry.Stack.FlatFppf.isIso_moduleLowerShriekAdjunction_unit`), but not the derived
module-level one.  It is therefore carried as three explicit hypotheses — a functor `Lsh`, an
adjunction `Lsh ⊣ g^*`, and invertibility of its unit, which is the assertion `g^* Lg_! = id` —
all three being exactly **Stacks 07AS** part (4).

The second input of the source's proof is that `Lg_! g^* K` again lies in
`D_{LQCoh^fbc}(𝒪_𝒳)`, which is **Stacks 07B9** parts (2)(a) and (2)(c) read in succession.
Neither is in the library — only part (2)(b),
`AlgebraicGeometry.Stack.FlatFppf.isZero_derivedModuleRestriction_iff`, which *is* the engine of
the proof below — so their joint consequence is carried as the explicit hypothesis
`hK' : D_{LQCoh^fbc}(𝒪_𝒳) (Lg_! g^* K)`.

Finally `D_{LQCoh^fbc}(𝒪_𝒳)` has to be a triangulated subcategory, so that the cone of a
morphism between two of its objects is again one of its objects.  That is **Stacks 0771**, the
weak Serre property of `LQCoh^fbc(𝒪_𝒳)`, which the library does not have either; as in
`AlgebraicGeometry.Stack.derivedQuasicoherentW_eq_trW` it is carried as the instance hypotheses
`[IsTriangulated]` and `[IsClosedUnderIsomorphisms]` on the subcategory.

### What the proof reuses

Everything geometric is **Stacks 07B9** (2)(b),
`AlgebraicGeometry.Stack.FlatFppf.isZero_derivedModuleRestriction_iff`: it turns both halves of
the conclusion into the single statement `g^* P = 0`.  For the cone that vanishing comes from
`g^* ε_K` being an isomorphism, by one triangle identity of the adjunction and
`CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁`; for the orthogonality it comes
from the adjunction isomorphism `Hom(Lg_! X, P') = Hom(X, g^* P')`.  The orthogonality is
recorded as `CategoryTheory.ObjectProperty.leftOrthogonal`, and the existential form as
`CategoryTheory.ObjectProperty.extensionProduct`, which are the notions
`StacksFrontier/CategoryTheory/Triangulated/AdmissibleSubcategories.lean` is written in: by
[Stacks, Tag 0H0P] there,
`AlgebraicGeometry.Stack.FlatFppf.extensionProduct_parasiticFreePart` together with
`AlgebraicGeometry.Stack.FlatFppf.leftOrthogonal_parasiticFreePart` says precisely that
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` is left admissible in `D_{LQCoh^fbc}(𝒪_𝒳)`.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
* [Stacks Project, Tag 07B9](https://stacks.math.columbia.edu/tag/07B9)
* [Stacks Project, Tag 07BA](https://stacks.math.columbia.edu/tag/07BA)
* [Stacks Project, Tag 0CQP](https://stacks.math.columbia.edu/tag/0CQP)
* [Stacks Project, Tag 0H0P](https://stacks.math.columbia.edu/tag/0H0P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w t t'

attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat isContinuous_inclusion_topology
  isCocontinuous_inclusion_topology hasSheafify_addCommGrpCat
  wEqualsLocallyBijective_addCommGrpCat hasSheafify_fppf_addCommGrpCat
  wEqualsLocallyBijective_fppf_addCommGrpCat hasSheafify_associatedTopology_ab
  wEqualsLocallyBijective_fppfTopology_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
  [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]
  [HasDerivedCategory.{t'} (flatFppfModules B S hS 𝒳)]
  (Lsh : DerivedCategory (flatFppfModules B S hS 𝒳) ⥤
    DerivedCategory (fppfModules B S hS 𝒳))
  (adj : Lsh ⊣ derivedModuleRestriction B S hS 𝒳)

/-- **The parasitic-free part `K' = Lg_! g^* K` of a complex of `𝒪_𝒳`-modules.**  Here `g^*` is
restriction to the flat-fppf site, `AlgebraicGeometry.Stack.FlatFppf.derivedModuleRestriction`,
and `Lg_!` is the derived lower shriek of **Stacks 07AS** part (4), carried as the hypothesis
`Lsh`.  This is the first term of the triangle of **Stacks 07BA**. -/
abbrev parasiticFreePart (K : DerivedCategory (fppfModules B S hS 𝒳)) :
    DerivedCategory (fppfModules B S hS 𝒳) :=
  Lsh.obj ((derivedModuleRestriction B S hS 𝒳).obj K)

/-- **The canonical morphism `Lg_! g^* K ⟶ K`**, the counit of the adjunction `Lg_! ⊣ g^*` of
**Stacks 07AS** part (4) at `K`.  Together with
`AlgebraicGeometry.Stack.FlatFppf.parasiticFreePart` this is the whole of the canonical data of
the triangle of **Stacks 07BA**: the third term is a cone on it, determined up to an isomorphism
of triangles inducing the identity on `K` by [Stacks, Tag 0CQP]. -/
def parasiticFreePartHom (K : DerivedCategory (fppfModules B S hS 𝒳)) :
    parasiticFreePart B S hS 𝒳 Lsh K ⟶ K :=
  adj.counit.app K

/-- **`g^*` inverts the canonical morphism `Lg_! g^* K ⟶ K`.**  By one of the triangle
identities, `g^*(ε_K)` is a retraction of the unit of `Lg_! ⊣ g^*` at `g^* K`, and that unit is
an isomorphism — this is the assertion `g^* Lg_! = id` of **Stacks 07AS** part (4), carried as
the hypothesis `hunit`. -/
theorem isIso_derivedModuleRestriction_map_parasiticFreePartHom (hunit : IsIso adj.unit)
    (K : DerivedCategory (fppfModules B S hS 𝒳)) :
    IsIso ((derivedModuleRestriction B S hS 𝒳).map
      (parasiticFreePartHom B S hS 𝒳 Lsh adj K)) := by
  have := hunit
  have h₁ : IsIso (adj.unit.app ((derivedModuleRestriction B S hS 𝒳).obj K)) := inferInstance
  have h₂ : adj.unit.app ((derivedModuleRestriction B S hS 𝒳).obj K) ≫
      (derivedModuleRestriction B S hS 𝒳).map
        (parasiticFreePartHom B S hS 𝒳 Lsh adj K) = 𝟙 _ :=
    adj.right_triangle_components (Y := K)
  have h₃ : IsIso (adj.unit.app ((derivedModuleRestriction B S hS 𝒳).obj K) ≫
      (derivedModuleRestriction B S hS 𝒳).map
        (parasiticFreePartHom B S hS 𝒳 Lsh adj K)) := by
    rw [h₂]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_left
    (adj.unit.app ((derivedModuleRestriction B S hS 𝒳).obj K)) _

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

include adj in
/-- **Stacks 07BA**, the orthogonality of the first term.  Every morphism from
`K' = Lg_! g^* K` to an object `P'` of `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` vanishes, i.e. `K'` lies
in the left orthogonal of `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.

Indeed `Hom(Lg_! g^* K, P') = Hom(g^* K, g^* P')` by the adjunction, and `g^* P' = 0` by
**Stacks 07B9** (2)(b), so the right-hand group vanishes. -/
@[stacks 07BA "the orthogonality: Hom_D(𝒪_𝒳)(E', P') = 0 for every P' in D_(Parasitic ∩ \
LQCoh^fbc)(𝒪_𝒳), at E' = Lg_! g^* E; conditional on the derived module-level Lg_! of 07AS (4), \
carried as the hypotheses Lsh and adj"]
theorem leftOrthogonal_parasiticFreePart (K : DerivedCategory (fppfModules B S hS 𝒳)) :
    (derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).leftOrthogonal
      (parasiticFreePart B S hS 𝒳 Lsh K) := by
  intro P' f hP'
  have hz : IsZero ((derivedModuleRestriction B S hS 𝒳).obj P') :=
    (isZero_derivedModuleRestriction_iff B S hS 𝒳 (E := E) (h := h) P'
      (fun n => (hP' n).2)).2 hP'
  exact (adj.homEquiv _ P').injective (hz.eq_of_tgt _ _)

variable [(derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).IsTriangulated]
  [(derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).IsClosedUnderIsomorphisms]

/-- **Stacks 07BA**, the third term of the triangle.  Let `K` be an object of
`D_{LQCoh^fbc}(𝒪_𝒳)` whose parasitic-free part `K' = Lg_! g^* K` again lies in
`D_{LQCoh^fbc}(𝒪_𝒳)` — that is **Stacks 07B9** (2)(a) followed by (2)(c), carried as the
hypothesis `hK'`.  Then every cone `P` on the canonical morphism `ε_K : K' ⟶ K` lies in
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.

Local quasi-coherence with flat base change is two out of three in the triangle.  For the
parasitic half, `g^*` is exact hence triangulated, and it inverts `ε_K`, so the third term of the
image triangle vanishes: `g^* P = 0`, which is the parasitic condition by
**Stacks 07B9** (2)(b). -/
@[stacks 07BA "the cone: for E' = Lg_! g^* E and E' ⟶ E the counit, every distinguished triangle \
E' ⟶ E ⟶ P ⟶ E'[1] has P in D_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒳), and all three terms in \
D_LQCoh^fbc(𝒪_𝒳); conditional on the derived module-level Lg_! of 07AS (4) and on 07B9 (2)(a), \
(2)(c), carried as the hypotheses Lsh, adj, hunit and hK'"]
theorem derivedParasitic_obj₃_of_distTriang_parasiticFreePartHom (hunit : IsIso adj.unit)
    (K : DerivedCategory (fppfModules B S hS 𝒳))
    (hK : derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 K)
    (hK' : derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳
      (parasiticFreePart B S hS 𝒳 Lsh K))
    (P : DerivedCategory (fppfModules B S hS 𝒳)) (b : K ⟶ P)
    (c : P ⟶ (parasiticFreePart B S hS 𝒳 Lsh K)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (parasiticFreePartHom B S hS 𝒳 Lsh adj K) b c ∈
      distTriang (DerivedCategory (fppfModules B S hS 𝒳))) :
    derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 P := by
  have hP : derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 P :=
    (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ext_of_isTriangulatedClosed₃
      _ hT hK' hK
  refine (isZero_derivedModuleRestriction_iff B S hS 𝒳 (E := E) (h := h) P hP).1 ?_
  refine (Triangle.isZero₃_iff_isIso₁ _
    (Functor.map_distinguished (moduleRestriction B S hS 𝒳).mapDerivedCategory _ hT)).2 ?_
  exact isIso_derivedModuleRestriction_map_parasiticFreePartHom B S hS 𝒳 Lsh adj hunit K

/-- **Stacks 07BA**, in the shape the source states it.  Every object `K` of
`D_{LQCoh^fbc}(𝒪_𝒳)` whose parasitic-free part lies in `D_{LQCoh^fbc}(𝒪_𝒳)` fits in a
distinguished triangle

`K' ⟶ K ⟶ P ⟶ K'[1]`

with `P` in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` and `K'` in `D_{LQCoh^fbc}(𝒪_𝒳)` and left
orthogonal to `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.

This is the existential reading of the two statements above, obtained by completing the
canonical morphism `ε_K` to a distinguished triangle; `K'` and `ε_K` themselves are the
`AlgebraicGeometry.Stack.FlatFppf.parasiticFreePart` and
`AlgebraicGeometry.Stack.FlatFppf.parasiticFreePartHom` of the canonical triangle. -/
@[stacks 07BA "the existence of the triangle: every E in D_LQCoh^fbc(𝒪_𝒳) is an extension of an \
object of D_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒳) by an object of D_LQCoh^fbc(𝒪_𝒳) left orthogonal to \
it, the extension being the canonical one on Lg_! g^* E ⟶ E; conditional on the derived \
module-level Lg_! of 07AS (4) and on 07B9 (2)(a), (2)(c)"]
theorem extensionProduct_parasiticFreePart (hunit : IsIso adj.unit)
    (K : DerivedCategory (fppfModules B S hS 𝒳))
    (hK : derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 K)
    (hK' : derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳
      (parasiticFreePart B S hS 𝒳 Lsh K)) :
    (((derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).leftOrthogonal ⊓
        derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).extensionProduct
      (derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳)) K := by
  obtain ⟨P, b, c, hT⟩ :=
    distinguished_cocone_triangle (parasiticFreePartHom B S hS 𝒳 Lsh adj K)
  exact ⟨_, P, _, b, c, hT,
    ⟨leftOrthogonal_parasiticFreePart B S hS 𝒳 Lsh adj E h K, hK'⟩,
    derivedParasitic_obj₃_of_distTriang_parasiticFreePartHom B S hS 𝒳 Lsh adj E h hunit K hK hK'
      P b c hT⟩

end AlgebraicGeometry.Stack.FlatFppf

end
