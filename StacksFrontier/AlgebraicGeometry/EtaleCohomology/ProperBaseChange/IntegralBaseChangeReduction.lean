module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.IntegralDirectImageAcyclic

/-!
# Reducing derived base change along an integral morphism to the underived comparison

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes in which `f` and `f'` are integral — finite, for instance.
Then the **derived** base change map `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` of
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange` is an isomorphism as soon as the
**underived** comparison `g^{-1} f_* ⟶ f'_* (g')^{-1}` of
`Stacks.EtaleCohomology.etaleAbelianBaseChange` is one. No boundedness or torsion condition is
imposed on the complex: the conclusion is an isomorphism of functors on the whole unbounded
derived category, and it specialises to a single abelian sheaf placed in degree zero.

This is the formal half of the finite case of proper base change, Stacks 0A4E: that lemma
deduces its conclusion from the vanishing of the positive higher direct images of a finite
morphism, which is available here as
`Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_isIntegralHom`, together
with the sheaf-level identification `g^{-1} f_* F = f'_* (g')^{-1} F` of Stacks 0959. **The
latter is what is carried as a hypothesis here, and is why nothing in this file is tagged
0A4E.** The identification is proved in the library for sheaves of *sets* on the small étale
site of Stacks 021B — `AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans` — and that site is
not the site `AlgebraicGeometry.Scheme.smallEtaleTopology` of the present development; the two
have equivalent sheaf categories by `AlgebraicGeometry.SmallEtale.sheafEquiv`, but the
equivalence has not been shown to carry one base change comparison to the other.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isIso_etaleAbelianBaseChange`
  — the derived base change map is an isomorphism when the underived comparison is.
* `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isIso_etaleAbelianBaseChange`
  — the same at a single abelian sheaf in degree zero.
* `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isFinite_of_isIso`
  — the shape the dévissage of Stacks 0A4F consumes: a cartesian square with `f` finite, the
  finiteness of `f'` obtained by base change rather than assumed.

## Implementation notes

The proof is the uniqueness characterisation
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_fac` of the derived base change map, read
as an equation between two composites at a complex `K`. Four of the five factors appearing in
it are isomorphisms:

* the two exactness comparisons `CategoryTheory.Functor.mapDerivedCategoryFactorsh` for the
  inverse images `g^{-1}` and `(g')^{-1}`, which are isomorphisms because inverse image is
  exact;
* the derived-functor units of `Rf_*` and of `Rf'_*`, which are isomorphisms because `f` and
  `f'` are integral — this is
  `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedDirectImageUnit_of_isIntegralHom`, and it is
  the only place integrality is used;
* the degreewise comparison, which is an isomorphism because the underived one is: applying a
  natural transformation degreewise is functorial, so it carries an invertible transformation to
  an invertible one.

Cancelling the invertible factors leaves the component of the derived base change map at
`DerivedCategory.Qh.obj K` invertible, and every object of the unbounded derived category is of
that form, the localization functor being essentially surjective; invertibility transports along
the isomorphism to such an object by naturality.

## References

* [Stacks Project, Tag 0A4E](https://stacks.math.columbia.edu/tag/0A4E)
* [Stacks Project, Tag 0A4A](https://stacks.math.columbia.edu/tag/0A4A)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-- Applying an invertible natural transformation degreewise to complexes gives an invertible
natural transformation of the induced functors on homotopy categories: the construction is
functorial, so it carries the inverse to an inverse. -/
private theorem isIso_natTrans_mapHomotopyCategory {ι : Type*} {V W : Type*} [Category* V]
    [Category* W] [Preadditive V] [Preadditive W] {F G : V ⥤ W} [F.Additive] [G.Additive]
    (α : F ⟶ G) [IsIso α] (c : ComplexShape ι) :
    IsIso (NatTrans.mapHomotopyCategory α c) := by
  refine ⟨NatTrans.mapHomotopyCategory (inv α) c, ?_, ?_⟩
  · rw [← NatTrans.mapHomotopyCategory_comp, IsIso.hom_inv_id,
      NatTrans.mapHomotopyCategory_id]
  · rw [← NatTrans.mapHomotopyCategory_comp, IsIso.inv_hom_id,
      NatTrans.mapHomotopyCategory_id]

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- The degreewise base change comparison on homotopy categories is invertible as soon as the
underived comparison is: it is the underived one applied degreewise, conjugated by the two
comparison isomorphisms for the composition of functors on homotopy categories. -/
private theorem isIso_etaleAbelianHomotopyBaseChange
    [IsIso (etaleAbelianBaseChange.{u, v} f g g' f' h)] :
    IsIso (etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h) := by
  have : IsIso (NatTrans.mapHomotopyCategory (etaleAbelianBaseChange.{u, v} f g g' f' h)
      (ComplexShape.up ℤ)) :=
    isIso_natTrans_mapHomotopyCategory _ _
  rw [etaleAbelianHomotopyBaseChange]
  infer_instance

/-- The component of the derived base change map at a complex is invertible. -/
private theorem isIso_etaleAbelianDerivedBaseChange_app_Qh
    [IsIntegralHom f] [IsIntegralHom f']
    [IsIso (etaleAbelianBaseChange.{u, v} f g g' f' h)]
    (K : HomotopyCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (ComplexShape.up ℤ)) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
      (DerivedCategory.Qh.obj K)) := by
  have : IsIso (etaleAbelianDerivedDirectImageUnit.{u, v} f) :=
    isIso_etaleAbelianDerivedDirectImageUnit_of_isIntegralHom.{u, v} f
  have : IsIso (etaleAbelianDerivedDirectImageUnit.{u, v} f') :=
    isIso_etaleAbelianDerivedDirectImageUnit_of_isIntegralHom.{u, v} f'
  have : IsIso (etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h) :=
    isIso_etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h
  have key := etaleAbelianDerivedBaseChange_fac.{u, v} f g g' f' h K
  have hrw : (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
        (DerivedCategory.Qh.obj K) =
      inv ((etaleAbelianDerivedInverseImage.{u, v} g).map
          ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app K)) ≫
        inv ((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app
          (((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K)) ≫
        (DerivedCategory.Qh.map ((etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h).app K) ≫
          (etaleAbelianDerivedDirectImageUnit.{u, v} f').app
            (((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K) ≫
          (etaleAbelianDerivedDirectImage.{u, v} f').map
            ((etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv.app K)) := by
    rw [← key]
    simp
  rw [hrw]
  infer_instance

/-- **The derived base change map along an integral morphism is an isomorphism as soon as the
underived comparison is.** For a commutative square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
of schemes with `f` and `f'` integral — finite, for instance — invertibility of the underived
comparison `g^{-1} f_* ⟶ f'_* (g')^{-1}` of
`Stacks.EtaleCohomology.etaleAbelianBaseChange` implies invertibility of the derived base change
map `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` on the whole unbounded derived category.

This carries the sheaf-level identification of Stacks 0959 as a hypothesis; it is the formal
half of Stacks 0A4E and not that lemma, which is why it bears no tag. -/
public theorem isIso_etaleAbelianDerivedBaseChange_of_isIso_etaleAbelianBaseChange
    [IsIntegralHom f] [IsIntegralHom f']
    (hbc : IsIso (etaleAbelianBaseChange.{u, v} f g g' f' h)) :
    IsIso (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h) := by
  have := hbc
  have hall : ∀ Z, IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app Z) := by
    intro Z
    obtain ⟨K, ⟨e⟩⟩ :=
      Functor.EssSurj.mem_essImage (F := DerivedCategory.Qh) (Y := Z) (self := inferInstance)
    have : IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
        (DerivedCategory.Qh.obj K)) :=
      isIso_etaleAbelianDerivedBaseChange_app_Qh.{u, v} f g g' f' h K
    have hnat := (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).naturality e.hom
    have hrw : (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app Z =
        inv ((etaleAbelianDerivedDirectImage.{u, v} f ⋙
            etaleAbelianDerivedInverseImage.{u, v} g).map e.hom) ≫
          (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
            (DerivedCategory.Qh.obj K) ≫
          (etaleAbelianDerivedInverseImage.{u, v} g' ⋙
            etaleAbelianDerivedDirectImage.{u, v} f').map e.hom := by
      rw [← hnat, IsIso.inv_hom_id_assoc]
    rw [hrw]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The base change map of a single abelian sheaf placed in degree zero is an isomorphism, under
the same hypotheses: it is a component of
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`. -/
public theorem isIso_etaleAbelianSheafDerivedBaseChange_of_isIso_etaleAbelianBaseChange
    [IsIntegralHom f] [IsIntegralHom f']
    (hbc : IsIso (etaleAbelianBaseChange.{u, v} f g g' f' h))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' h F) := by
  have := isIso_etaleAbelianDerivedBaseChange_of_isIso_etaleAbelianBaseChange.{u, v}
    f g g' f' h hbc
  rw [etaleAbelianSheafDerivedBaseChange]
  infer_instance

/-- The shape the dévissage of Stacks 0A4F consumes: for a **cartesian** square with `f` finite,
and granted the sheaf-level identification of Stacks 0959 for that square, the base change map
`g^{-1} Rf_* F ⟶ Rf'_* (g')^{-1} F` is an isomorphism for every abelian sheaf `F` on the small
étale site of `X`.

Finiteness of `f'` is not assumed: it is the base change of `f` along `g`, and finiteness is
stable under base change. Only integrality of the two is used. The hypothesis `hbc` is Stacks
0959 for the square, which is the one input of Stacks 0A4E that the library does not supply at
this site presentation; see the module documentation. -/
public theorem isIso_etaleAbelianSheafDerivedBaseChange_of_isFinite_of_isIso
    (sq : IsPullback g' f' f g) [IsFinite f]
    (hbc : IsIso (etaleAbelianBaseChange.{u, v} f g g' f' sq.w))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' sq.w F) := by
  have : IsFinite f' :=
    MorphismProperty.of_isPullback (P := @IsFinite) sq inferInstance
  exact isIso_etaleAbelianSheafDerivedBaseChange_of_isIso_etaleAbelianBaseChange.{u, v}
    f g g' f' sq.w hbc F

end Stacks.EtaleCohomology

end
