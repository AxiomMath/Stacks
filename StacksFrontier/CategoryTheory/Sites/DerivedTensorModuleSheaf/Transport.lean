module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Basic
public import StacksFrontier.Homology.TotalComplexTransport

/-!
# Exact monoidal functors and the derived tensor product of sheaves of modules

Let `G` be an exact functor from sheaves of `Λ`-modules on a site `(C, J)` to sheaves of
`Λ`-modules on a site `(C', J')`, which commutes with colimits, carries the tensor product to the
tensor product, and carries sheafifications of presheaves of free modules to sheafifications of
presheaves of free modules. Then for `K` in `D(C, Λ)` and `L` bounded above in `D(C, Λ)`

`G(K ⊗_Λ^L L) ≅ G(K) ⊗_Λ^L G(L)`.

Restriction to a slice site and inverse image along a morphism of sites are such functors, and
this is the form in which the derived tensor product is compared with its restrictions.

## Main results

* `Stacks.ModuleSheaf.nonempty_mapDerivedCategory_tensor_iso`: the comparison, for a bounded
  above right factor.
* `Stacks.ModuleSheaf.nonempty_homology_mapDerivedCategory_tensor_iso`: its consequence for
  cohomology sheaves, `G(Hⁿ(K ⊗_Λ^L L)) ≅ Hⁿ(G(K) ⊗_Λ^L G(L))`.

## Implementation notes

The two sites have independent universes, each dominated by the universe of the module
sections. With two universe inequalities in the context, instance search can match the wrong one
when the universes of a constant are not yet determined, so the constants of the derived tensor
product are written with explicit universe arguments.

The right factor is represented by a bounded above complex of sheafified presheaves of free
modules (Stacks 05T7), which is K-flat, so the derived tensor product is the total tensor complex
of an arbitrary representative of the left factor with it
(`Stacks.ModuleSheaf.derivedTensorIsoOfKFlat`); `G` carries that total complex to the total
complex of the images (`CategoryTheory.Functor.mapBifunctorTotalIso`), whose right factor is
again a bounded above complex of sheafified presheaves of free modules, hence K-flat. The
comparison of the tensor products is taken as a family of isomorphisms with its two naturality
squares, which is the form in which inverse image functors supply it.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.KFlatBifunctor

universe t t' w v u v' u'

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory derivedMonoidal

/-- An additive functor preserves strict boundedness above of complexes. -/
theorem isStrictlyLE_mapHomologicalComplex {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] [HasZeroObject A] [HasZeroObject B]
    (G : A ⥤ B) [G.Additive] (K : CochainComplex A ℤ) (a : ℤ) [K.IsStrictlyLE a] :
    CochainComplex.IsStrictlyLE ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact G.map_isZero (K.isZero_of_isStrictlyLE a i hi)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  {Λ : Type w} [CommRing Λ] [UnivLE.{max u v, w}] [UnivLE.{max u' v', w}]

variable [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]
  [HasDerivedCategory.{t'} (Sheaf J' (ModuleCat.{w} Λ))]
  (G : Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf J' (ModuleCat.{w} Λ)) [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] [PreservesColimitsOfSize.{0, 0} G]
  (ε : ∀ M N : Sheaf J (ModuleCat.{w} Λ), G.obj (M ⊗ N) ≅ G.obj M ⊗ G.obj N)
  (hε₁ : ∀ {M M' : Sheaf J (ModuleCat.{w} Λ)} (f : M ⟶ M') (N : Sheaf J (ModuleCat.{w} Λ)),
    G.map (f ▷ N) ≫ (ε M' N).hom = (ε M N).hom ≫ G.map f ▷ G.obj N)
  (hε₂ : ∀ (M : Sheaf J (ModuleCat.{w} Λ)) {N N' : Sheaf J (ModuleCat.{w} Λ)} (g : N ⟶ N'),
    G.map (M ◁ g) ≫ (ε M N').hom = (ε M N).hom ≫ G.obj M ◁ G.map g)
  (hG : ∀ M, sheafifiedFree.{w, v, u} J Λ M → sheafifiedFree.{w, v', u'} J' Λ (G.obj M))

include hε₁ hε₂ hG in
/-- **An exact monoidal functor carrying sheafified presheaves of free modules to sheafified
presheaves of free modules commutes with the derived tensor product** of an arbitrary object
with a bounded above object. -/
theorem nonempty_mapDerivedCategory_tensor_iso
    (K L : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (b : ℤ) [L.IsLE b] :
    Nonempty (G.mapDerivedCategory.obj (K ⊗ L) ≅
      G.mapDerivedCategory.obj K ⊗ G.mapDerivedCategory.obj L) := by
  obtain ⟨F', hF', hF'LE, ⟨eF'⟩⟩ := exists_kFlat_isStrictlyLE_representative.{t, w, v, u} L b
  let N := DerivedCategory.Q.objPreimage K
  let eN : DerivedCategory.Q.obj N ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hGF' := isStrictlyLE_mapHomologicalComplex G F' b
  let T : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (N ⊗ F') ≅
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N ⊗
        (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj F' :=
    Functor.mapBifunctorTotalIso (curriedTensor _) (curriedTensor _) G G G ε
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) hε₁ hε₂ N F'
  exact ⟨G.mapDerivedCategory.mapIso ((eN ⊗ᵢ eF').symm ≪≫
      derivedTensorIsoOfKFlat.{t, w, v, u} N (kFlat_of_isStrictlyLE.{w, v, u} F' b hF')) ≪≫
    G.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso T ≪≫
    (derivedTensorIsoOfKFlat.{t', w, v', u'} _
      (kFlat_of_isStrictlyLE.{w, v', u'} _ b (fun n => hG _ (hF' n)))).symm ≪≫
    ((G.mapDerivedCategoryFactors.app N).symm ⊗ᵢ (G.mapDerivedCategoryFactors.app F').symm) ≪≫
    (G.mapDerivedCategory.mapIso eN ⊗ᵢ G.mapDerivedCategory.mapIso eF')⟩

include hε₁ hε₂ hG in
/-- The cohomology sheaves of the derived tensor product are compatible with an exact monoidal
functor carrying sheafified presheaves of free modules to such: for `L` bounded above,
`G(Hⁿ(K ⊗_Λ^L L)) ≅ Hⁿ(G(K) ⊗_Λ^L G(L))`. -/
theorem nonempty_homology_mapDerivedCategory_tensor_iso
    (K L : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (b : ℤ) [L.IsLE b] (n : ℤ) :
    Nonempty (G.obj ((DerivedCategory.homologyFunctor _ n).obj (K ⊗ L)) ≅
      (DerivedCategory.homologyFunctor _ n).obj
        (G.mapDerivedCategory.obj K ⊗ G.mapDerivedCategory.obj L)) := by
  obtain ⟨e⟩ := nonempty_mapDerivedCategory_tensor_iso G ε hε₁ hε₂ hG K L b
  exact ⟨((G.mapDerivedCategoryHomologyIso n).app (K ⊗ L)).symm ≪≫
    (DerivedCategory.homologyFunctor _ n).mapIso e⟩

omit hε₁ hε₂ in
include hG in
/-- `Stacks.ModuleSheaf.nonempty_homology_mapDerivedCategory_tensor_iso` for a monoidal functor,
whose tensor comparison is the inverse of its monoidal structure. -/
theorem nonempty_homology_mapDerivedCategory_tensor_iso_of_monoidal [G.Monoidal]
    (K L : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (b : ℤ) [L.IsLE b] (n : ℤ) :
    Nonempty (G.obj ((DerivedCategory.homologyFunctor _ n).obj (K ⊗ L)) ≅
      (DerivedCategory.homologyFunctor _ n).obj
        (G.mapDerivedCategory.obj K ⊗ G.mapDerivedCategory.obj L)) :=
  nonempty_homology_mapDerivedCategory_tensor_iso G (fun M N => (Functor.Monoidal.μIso G M N).symm)
    (fun f N => by simp)
    (fun M _ _ g => by simp) hG K L b n

end Stacks.ModuleSheaf
