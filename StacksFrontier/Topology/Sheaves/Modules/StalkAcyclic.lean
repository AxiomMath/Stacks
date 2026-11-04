module

public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness

/-!
# Acyclicity of a complex of sheaves of modules is a stalkwise condition, over the stalk ring

Let `𝒪` be a sheaf of rings on a topological space `X`. A cochain complex of sheaves of
`𝒪`-modules is acyclic precisely when, for every `x : X`, the complex of `𝒪_x`-modules
obtained by taking stalks at `x` degreewise is acyclic.

This is the module-valued form of Stacks 01AG. The form already available,
`AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact`, deliberately tests
exactness of the stalk complex in `AddCommGrpCat`: stalks of modules over a *varying* sheaf
of rings are most cheaply compared through their underlying abelian groups. But a statement
whose conclusion is a property of a complex *of modules over the stalk ring* — K-flatness of
`K_x` over `𝒪_x`, Stacks 06YB being the case at hand — cannot consume that form, because the
complex it speaks about is the one built by
`AlgebraicGeometry.SheafOfModules.stalkFunctor`, whose values are `ModuleCat 𝒪_x`.

The bridge is that forgetting the module structure changes neither exactness nor the complex:
`stalkFunctor 𝒪 x ⋙ forget₂ (ModuleCat 𝒪_x) AddCommGrpCat` is `stalkAddCommGroupFunctor 𝒪 x`
on the nose (`stalkFunctor_comp_forget₂`), and `forget₂ (ModuleCat 𝒪_x) AddCommGrpCat` is a
faithful exact functor, so it neither creates nor destroys exactness of a short complex.

## Main results

* `AlgebraicGeometry.SheafOfModules.stalkFunctor_additive`: the stalk functor is additive, so
  it may be applied to a complex degreewise at all.
* `AlgebraicGeometry.SheafOfModules.exactAt_iff_forall_stalk_exactAt`: exactness of a complex
  of sheaves of modules in one degree, tested on stalks over the stalk ring.
* `AlgebraicGeometry.SheafOfModules.acyclic_iff_forall_stalk_acyclic`: acyclicity of a complex
  of sheaves of modules, tested on stalks over the stalk ring.
* `AlgebraicGeometry.SheafOfModules.isIso_iff_forall_isIso_stalkFunctor_map`: isomorphy of a
  morphism of sheaves of modules, tested on stalks over the stalk ring.
* `AlgebraicGeometry.SheafOfModules.quasiIsoAt_iff_forall_stalk_quasiIsoAt` and
  `AlgebraicGeometry.SheafOfModules.quasiIso_iff_forall_stalk_quasiIso`: a morphism of
  complexes of sheaves of modules is a quasi-isomorphism in degree `i`, respectively a
  quasi-isomorphism, exactly when all of its maps of stalk complexes are.

## Implementation notes

Additivity of the stalk functor is not available by synthesis and is obtained here from
`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits`: a functor preserving binary
coproducts between preadditive categories with binary biproducts preserves binary biproducts,
hence is additive. Going through the composite with `forget₂` instead does not work, since
`stalkAddCommGroupFunctor` is a `def` and synthesis will not unfold it to find the three
additive factors.

The degreewise statement is arranged so that no transport is needed. Both
`((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).sc i = (K.sc i).map F` and
`ShortComplex.map_comp` hold by `rfl`, so the two short complexes being compared — the `i`-th
short complex of the stalk complex, and the stalk short complex of the `i`-th short complex —
are literally a short complex and its image under `forget₂`, and the comparison is exactly
`ShortComplex.exact_map_iff_of_faithful`.

The quasi-isomorphism criterion is not deduced from the acyclicity one through mapping cones.
A single stalk functor does not reflect isomorphisms, so Mathlib's
`HomologicalComplex.quasiIso_map_iff_of_preservesHomology` does not apply; instead the stalk
functors are used jointly, through the fact that they collectively detect isomorphisms. The
transport of homology along one of them is Mathlib's `ShortComplex.homologyFunctorIso`, which
is available because the stalk functor is exact, and the degreewise short complexes on the two
sides agree by `rfl` as above.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  (𝒪 : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)

/-- The stalk functor on sheaves of modules is additive.

This is not available by synthesis: `stalkFunctor` is a `def` built by hand out of `stalkObj`
and `stalkMap`, so nothing exposes its action on sums. It is deduced instead from the fact
that it preserves colimits (`stalkFunctor_preservesColimits`, Stacks 01AH): a functor between
preadditive categories with binary biproducts which preserves binary coproducts preserves
binary biproducts, and a functor preserving binary biproducts is additive.

Without this instance the stalk functor cannot be applied to a complex degreewise at all,
since `Functor.mapHomologicalComplex` requires an additive functor. -/
instance stalkFunctor_additive : (stalkFunctor 𝒪 x).Additive :=
  haveI := preservesBinaryBiproducts_of_preservesBinaryCoproducts (stalkFunctor 𝒪 x)
  Functor.additive_of_preservesBinaryBiproducts _

/-- Taking stalks at `x` over the stalk ring and then forgetting the module structure is
taking stalks of the underlying presheaf of abelian groups: the `ModuleCat 𝒪_x`-valued stalk
functor of `Colimits.lean` and the `AddCommGrpCat`-valued one of `Exactness.lean` agree after
`forget₂`, by definition.

Everything in this file flows through this equation; it is what lets the `AddCommGrpCat`-valued
stalk criterion for exactness be read as a statement about complexes of `𝒪_x`-modules. -/
theorem stalkFunctor_comp_forget₂ :
    stalkFunctor 𝒪 x ⋙
        forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) 𝒪.obj x))
          AddCommGrpCat.{u} =
      stalkAddCommGroupFunctor 𝒪 x :=
  rfl

/-- The short complex of `𝒪_x`-modules cut out of the stalk complex in degree `i` is exact
exactly when the short complex of abelian groups cut out of `K` in degree `i` and then
stalked at `x` is: the second is the image of the first under the faithful exact functor
`forget₂ (ModuleCat 𝒪_x) AddCommGrpCat`, by `stalkFunctor_comp_forget₂`. -/
theorem exact_stalk_sc_iff_stalkShortComplex_exact
    (K : CochainComplex (_root_.SheafOfModules.{u} 𝒪) ℤ) (i : ℤ) :
    ((((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).sc i).Exact ↔
      (stalkShortComplex 𝒪 (K.sc i) x).Exact :=
  (((K.sc i).map (stalkFunctor 𝒪 x)).exact_map_iff_of_faithful
    (forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) 𝒪.obj x))
      AddCommGrpCat.{u})).symm

/-- A cochain complex of sheaves of `𝒪`-modules is exact in degree `i` if and only if, for
every point `x`, the complex of `𝒪_x`-modules of stalks at `x` is exact in degree `i`.

This is the module-valued form of the stalk criterion
`exact_iff_stalkShortComplex_exact` (Stacks 01AG). -/
theorem exactAt_iff_forall_stalk_exactAt
    (K : CochainComplex (_root_.SheafOfModules.{u} 𝒪) ℤ) (i : ℤ) :
    K.ExactAt i ↔ ∀ x : X,
      (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff, exact_iff_stalkShortComplex_exact]
  exact forall_congr' fun x => (exact_stalk_sc_iff_stalkShortComplex_exact 𝒪 x K i).symm

/-- **Stalkwise acyclicity, over the stalk ring.** A cochain complex of sheaves of
`𝒪`-modules is acyclic if and only if, for every point `x` of `X`, the cochain complex of
`𝒪_x`-modules obtained by taking stalks at `x` in each degree is acyclic.

This is the module-valued form of Stacks 01AG, and the shape in which the stalk criterion is
consumed by statements about complexes of modules over the stalk ring — notably Stacks 06YB,
where the conclusion to be reached about `K_x` is K-flatness over `𝒪_x`. -/
theorem acyclic_iff_forall_stalk_acyclic (K : CochainComplex (_root_.SheafOfModules.{u} 𝒪) ℤ) :
    K.Acyclic ↔ ∀ x : X,
      (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  constructor
  · intro h x i
    exact (exactAt_iff_forall_stalk_exactAt 𝒪 K i).1 (h i) x
  · intro h i
    exact (exactAt_iff_forall_stalk_exactAt 𝒪 K i).2 fun x => h x i

/-- **Isomorphy is stalkwise, over the stalk ring.** A morphism of sheaves of `𝒪`-modules is an
isomorphism if and only if, for every point `x` of `X`, the induced map of stalks at `x` is an
isomorphism of `𝒪_x`-modules. -/
theorem isIso_iff_forall_isIso_stalkFunctor_map
    {M N : _root_.SheafOfModules.{u} 𝒪} (g : M ⟶ N) :
    IsIso g ↔ ∀ x : X, IsIso ((stalkFunctor 𝒪 x).map g) := by
  rw [isIso_iff_bijective_stalkMap]
  exact forall_congr' fun x => (ConcreteCategory.isIso_iff_bijective _).symm

/-- The map induced in degree `i` on homology by a morphism of cochain complexes of sheaves of
`𝒪`-modules is an isomorphism if and only if, for every point `x` of `X`, the map induced in
degree `i` on homology by the corresponding morphism of complexes of stalks is.

The stalk functor is exact, so it commutes with homology; isomorphy is then detected on stalks. -/
theorem isIso_homologyMap_iff_forall_stalk
    {K L : CochainComplex (_root_.SheafOfModules.{u} 𝒪) ℤ} (f : K ⟶ L) (i : ℤ) :
    IsIso (HomologicalComplex.homologyMap f i) ↔ ∀ x : X,
      IsIso (HomologicalComplex.homologyMap
        (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).map f) i) := by
  rw [isIso_iff_forall_isIso_stalkFunctor_map]
  exact forall_congr' fun x => (NatIso.isIso_map_iff
    (ShortComplex.homologyFunctorIso (stalkFunctor 𝒪 x))
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) i).map f)).symm

/-- A morphism of cochain complexes of sheaves of `𝒪`-modules is a quasi-isomorphism in degree
`i` if and only if, for every point `x` of `X`, the morphism of complexes of `𝒪_x`-modules
obtained by taking stalks at `x` in each degree is. -/
theorem quasiIsoAt_iff_forall_stalk_quasiIsoAt
    {K L : CochainComplex (_root_.SheafOfModules.{u} 𝒪) ℤ} (f : K ⟶ L) (i : ℤ) :
    QuasiIsoAt f i ↔ ∀ x : X,
      QuasiIsoAt (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).map f) i := by
  rw [_root_.quasiIsoAt_iff_isIso_homologyMap, isIso_homologyMap_iff_forall_stalk]
  exact forall_congr' fun x => (_root_.quasiIsoAt_iff_isIso_homologyMap _ i).symm

/-- **Stalkwise criterion for quasi-isomorphy, over the stalk ring.** A morphism of cochain
complexes of sheaves of `𝒪`-modules is a quasi-isomorphism if and only if, for every point `x`
of `X`, the morphism of complexes of `𝒪_x`-modules obtained by taking stalks at `x` in each
degree is a quasi-isomorphism.

This is Stacks 08TL, the stalk criterion of Stacks 01AG applied to complexes. -/
theorem quasiIso_iff_forall_stalk_quasiIso
    {K L : CochainComplex (_root_.SheafOfModules.{u} 𝒪) ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ ∀ x : X,
      QuasiIso (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  simp only [_root_.quasiIso_iff]
  exact ⟨fun h x i => (quasiIsoAt_iff_forall_stalk_quasiIsoAt 𝒪 f i).1 (h i) x,
    fun h i => (quasiIsoAt_iff_forall_stalk_quasiIsoAt 𝒪 f i).2 fun x => h x i⟩

/-- A morphism of cochain complexes of sheaves of `𝒪`-modules all of whose maps of stalk
complexes are quasi-isomorphisms is itself a quasi-isomorphism.

The converse implication, that the stalk functor carries a quasi-isomorphism to one, is
`HomologicalComplex.quasiIso_map_of_preservesHomology`. -/
theorem quasiIso_of_forall_stalk_quasiIso
    {K L : CochainComplex (_root_.SheafOfModules.{u} 𝒪) ℤ} (f : K ⟶ L)
    (h : ∀ x : X,
      QuasiIso (((stalkFunctor 𝒪 x).mapHomologicalComplex (ComplexShape.up ℤ)).map f)) :
    QuasiIso f :=
  (quasiIso_iff_forall_stalk_quasiIso 𝒪 f).2 h

end AlgebraicGeometry.SheafOfModules

end

end
