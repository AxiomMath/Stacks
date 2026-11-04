module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.ExtendScalarsCancel
public import StacksFrontier.RingTheory.MilnorPatching.Relative
import StacksFrontier.Homology.HomComplex.RHom.BaseChange
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.ProjectionFormula

/-!
# The projection formula at the two ring maps of a pushout square

`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.Tensor` carries the projection
formula for one ring map: extension of scalars along `g : S → T` followed by restriction of
scalars back to `S` is tensoring with `T`.  Every statement in that file, and every statement in
this directory that evaluates a component of it, is about a *single* ring map.

The keystone `Dualizing.TensorComparisonCompatibility` is not.  It is read across a square

```
S --g--> T
|        |
p        w
v        v
S' --h-> T'
```

of commutative rings, and after the reductions of
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail` what remains of it is an equation between
the projection formula at `g` and the projection formula at `h`, the two being compared by the
base change along `p`.  Nothing in the directory pairs two instances of the projection formula,
and this file supplies that pairing on *modules*, which is where the mathematical content of it
sits: both composites send `s ⊗ (t ⊗ m)` to `(h s · w t) ⊗ (1 ⊗ m)`.

The square has to be a pushout — `T'` has to be `S' ⊗_S T` — for the statement to be true at all:
the left-hand side lands in `S' ⊗_S T` tensored with the base change of `M`, the right-hand side
in `T'` tensored with it, and `Dualizing.pushoutAlgebraIso` is the identification of the two,
which exists exactly because the square is a pushout.  The hypothesis is
`MilnorPatching.IsPushoutSquare`, which `MilnorPatching.algebraMap_isPushoutSquare` and
`MilnorPatching.tensorPushout` supply for the square the keystone is read at.

**What is not done here.**  This is the module-level identity, not the chain-level one and not the
derived one; `Dualizing.TensorComparisonCompatibility` is not proved and no tag loses its
conditional caveat.  The two steps still owed are recorded in the implementation notes.

## Main definitions

* `Dualizing.extendRestrictScalarsModuleIso` — the projection formula for a ring map on modules,
  a public name for the statement proved `private` in
  `StacksFrontier.Homology.HomComplex.RHom.BaseChange`, which is what
  `Dualizing.extendRestrictScalarsComplexIso` is the degreewise form of.
* `Dualizing.extendScalarsSquareIso` — the two extensions of scalars across a commuting square
  agree, both being extension along the diagonal.
* `Dualizing.pushoutAlgebraIso` — the base change of the algebra: `S' ⊗_S T` is `T'`.

## Main results

* `Dualizing.extendRestrictScalarsModuleIso_square` — **the pairing**: the projection formula at
  `g`, base-changed along `p` and composed with `Dualizing.pushoutAlgebraIso`, is the projection
  formula at `h` read across the square.
* `Dualizing.extendRestrictScalarsModuleIso_square_lhs_apply` and `…_rhs_apply` — the common
  value of the two composites on a pure tensor, which is what the pairing says.
* `Dualizing.pushoutAlgebraIso_hom_tmul` — the base change of the algebra sends `s ⊗ t` to
  `h s · w t`.

## Implementation notes

The equation is stated with the square comparisons read in the direction in which every factor
has an element formula: `MilnorPatching.pushoutBaseChangeIso_inv_tmul` evaluates the pushout
comparison only on `inv`, and `TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul` the
extension comparison only on pure tensors of its source.  Read the other way the composite starts
at `T' ⊗_{S'} (S' ⊗_S M)`, whose general element `t' ⊗ (s' ⊗ m)` carries an arbitrary `t' : T'`
that no formula in sight decomposes; the orientation chosen here starts at `S' ⊗_S (T ⊗_S M)`,
where `TensorProduct.ext_threefold'` reduces the check to pure tensors outright.  All four
isomorphisms being invertible, the two readings are interchangeable, so nothing is lost.

The ext step is `(ModuleCat.restrictScalars p).map_injective` followed by
`TensorProduct.ext_threefold'` rather than `ModuleCat.ExtendScalars.hom_ext`: the latter fixes
the outer tensor factor at `1` and leaves an induction over the inner factor, in which
`TensorProduct.tmul_zero` does not fire — the `Module S` instance on the first factor of
`ModuleCat.extendScalars` is `Module.compHom` of the ring map, not the one `rw` finds at its
transparency, and the rewrite reports the pattern absent with the goal printing identically to
one it would close.  Restricting scalars first makes both sides `S`-linear, and then the
threefold ext lemma supplies all of the additivity.

**The two steps still owed.**  Lifting this to `Dualizing.derivedExtendRestrictScalarsTensorIso`
at the two ring maps of the square needs, in order:

* the *chain-level* pairing — the same statement for
  `Dualizing.extendRestrictScalarsComplexIso`.  It does not follow degreewise from this one:
  that isomorphism is the degreewise projection formula composed with two braidings of the
  Koszul-signed monoidal structure on cochain complexes and with a comparison of termwise
  tensoring against tensoring with a single complex, while the base change of a total tensor
  product is `CochainComplex.ExtendScalars.extendScalarsMonoidalIso`, assembled over the
  antidiagonal.  So the pairing has to be checked on the summand of each bidegree, where the
  Koszul signs of the two sides have to be reconciled; this module-level identity is what it
  reduces to on each summand.
* the *derived* pairing — the same statement for
  `Dualizing.derivedExtendRestrictScalarsTensorIsoEqualUniverse`, which by
  `Dualizing.derivedExtendRestrictScalarsTensorIsoEqualUniverse_hom_app` is the chain-level
  pairing together with a reconciliation of the comparison morphisms of the two derived
  extensions of scalars, of the two components of
  `CategoryTheory.Functor.mapDerivedCategoryFactors`, and of the two tensor comparisons of the
  K-flat models.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open scoped ChangeOfRings TensorProduct

universe u

namespace Dualizing

variable {S T S' T' : Type u} [CommRing S] [CommRing T] [CommRing S'] [CommRing T']

/-- **The projection formula for a ring map, on modules.** Extension of scalars along
`g : S → T` followed by restriction of scalars back to `S` is tensoring with `T` viewed as an
`S`-module. This is the module-level statement underlying
`Dualizing.extendRestrictScalarsComplexIso`; it is `private` in
`StacksFrontier.Homology.HomComplex.RHom.BaseChange` and is named here so that it can appear in a
statement. -/
@[no_expose]
noncomputable def extendRestrictScalarsModuleIso (g : S →+* T) :
    ModuleCat.extendScalars.{u, u, u} g ⋙ ModuleCat.restrictScalars g ≅
      tensorLeft ((ModuleCat.restrictScalars g).obj (ModuleCat.of T T)) :=
  Stacks.DerivedHom.BaseChangeIso.extensionRestrictionIso g

private theorem extensionRestrictionIso_hom_app_apply (g : S →+* T) (M : ModuleCat.{u} S)
    (x : (ModuleCat.extendScalars.{u, u, u} g ⋙ ModuleCat.restrictScalars g).obj M) :
    (Stacks.DerivedHom.BaseChangeIso.extensionRestrictionIso g).hom.app M x = x :=
  rfl

/-- The module-level projection formula changes no element: both sides of
`Dualizing.extendRestrictScalarsModuleIso` are `T ⊗_S M`, and the isomorphism only re-reads the
`S`-action on it. -/
theorem extendRestrictScalarsModuleIso_hom_app_apply (g : S →+* T) (M : ModuleCat.{u} S)
    (x : (ModuleCat.extendScalars.{u, u, u} g ⋙ ModuleCat.restrictScalars g).obj M) :
    (extendRestrictScalarsModuleIso g).hom.app M x = x :=
  extensionRestrictionIso_hom_app_apply g M x

section Square

variable (g : S →+* T) (p : S →+* S') (w : T →+* T') (h : S' →+* T')
  (comm : w.comp g = h.comp p)

/-- **The two extensions of scalars across a commuting square agree.** For a commuting square
`w ∘ g = h ∘ p` of commutative rings, extending along the top and then the right edge is
extending along the left and then the bottom edge: both are extension of scalars along the
diagonal `w ∘ g`. This is `Stacks.ModuleCat.cancelIso` at the two factorizations of that
diagonal, which is why the composite is spelled `w.comp g` on both sides rather than being
transported by an `eqToIso`. -/
noncomputable def extendScalarsSquareIso :
    ModuleCat.extendScalars.{u, u, u} p ⋙ ModuleCat.extendScalars.{u, u, u} h ≅
      ModuleCat.extendScalars.{u, u, u} g ⋙ ModuleCat.extendScalars.{u, u, u} w :=
  Stacks.ModuleCat.cancelIso p h (w.comp g)
      (fun x => by rw [comm]; rfl) ≪≫
    (Stacks.ModuleCat.cancelIso g w (w.comp g) (fun _ => rfl)).symm

/-- **The lifted algebra of a pushout square.** For a pushout square `w ∘ g = h ∘ p`, extending
`T` along `p` gives `T'`: the square being a pushout says exactly that `S' ⊗_S T` is `T'`. This
is `MilnorPatching.pushoutBaseChangeIso` at the free module of rank one over `T`, followed by
`ModuleCat.ExtendScalars.objSelfIso`. -/
noncomputable def pushoutAlgebraIso
    (hp : MilnorPatching.IsPushoutSquare g p w h comm) :
    (ModuleCat.extendScalars.{u, u, u} p).obj
        ((ModuleCat.restrictScalars g).obj (ModuleCat.of T T)) ≅
      (ModuleCat.restrictScalars h).obj (ModuleCat.of T' T') :=
  (MilnorPatching.pushoutBaseChangeIso g p w h comm hp (ModuleCat.of T T)).symm ≪≫
    (ModuleCat.restrictScalars h).mapIso (ModuleCat.ExtendScalars.objSelfIso w)

/-- The lifted algebra isomorphism sends `s ⊗ t` to `h s · w t`. -/
theorem pushoutAlgebraIso_hom_tmul
    (hp : MilnorPatching.IsPushoutSquare g p w h comm) (s : S')
    (t : (ModuleCat.restrictScalars g).obj (ModuleCat.of T T)) :
    (pushoutAlgebraIso g p w h comm hp).hom (s ⊗ₜ[S,p] t) = h s * w t :=
  Eq.trans
    (congrArg (fun z : (ModuleCat.extendScalars.{u, u, u} w).obj (ModuleCat.of T T) =>
        (ModuleCat.ExtendScalars.objSelfIso w).hom z)
      (MilnorPatching.pushoutBaseChangeIso_inv_tmul g p w h comm hp (ModuleCat.of T T) s t))
    (ModuleCat.ExtendScalars.objSelfIso_hom_tmul w (h s) (t : T))

private theorem pushoutBaseChange_inv_app_apply
    (hp : MilnorPatching.IsPushoutSquare g p w h comm) (N : ModuleCat.{u} T)
    (y : (ModuleCat.restrictScalars g ⋙ ModuleCat.extendScalars.{u, u, u} p).obj N) :
    (MilnorPatching.pushoutBaseChange g p w h comm hp).inv.app N y =
      (MilnorPatching.pushoutBaseChangeIso g p w h comm hp N).inv y :=
  rfl

private theorem extendScalarsSquareIso_inv_app_apply (M : ModuleCat.{u} S)
    (y : (ModuleCat.extendScalars.{u, u, u} g ⋙ ModuleCat.extendScalars.{u, u, u} w).obj M) :
    (extendScalarsSquareIso g p w h comm).inv.app M y =
      (Stacks.ModuleCat.cancelIsoApp p h (w.comp g) (fun x => by rw [comm]; rfl) M).inv
        ((Stacks.ModuleCat.cancelIsoApp g w (w.comp g) (fun _ => rfl) M).hom y) :=
  rfl

/-- The value of the projection formula over `S`, base-changed along `p` and composed with the
lifted algebra, on a pure tensor. -/
theorem extendRestrictScalarsModuleIso_square_lhs_apply
    (hp : MilnorPatching.IsPushoutSquare g p w h comm) (M : ModuleCat.{u} S) (s : S')
    (t : (ModuleCat.restrictScalars g).obj (ModuleCat.of T T)) (m : M) :
    ((ModuleCat.extendScalars.{u, u, u} p).map ((extendRestrictScalarsModuleIso g).hom.app M) ≫
          δ (ModuleCat.extendScalars.{u, u, u} p)
              ((ModuleCat.restrictScalars g).obj (ModuleCat.of T T)) M ≫
            (pushoutAlgebraIso g p w h comm hp).hom ▷
              ((ModuleCat.extendScalars.{u, u, u} p).obj M)) (s ⊗ₜ[S,p] (t ⊗ₜ[S] m)) =
      (show (ModuleCat.restrictScalars h).obj (ModuleCat.of T' T') from h s * w t) ⊗ₜ[S']
        (show (ModuleCat.extendScalars.{u, u, u} p).obj M from (1 : S') ⊗ₜ[S,p] m) :=
  congrArg (fun z : (ModuleCat.restrictScalars h).obj (ModuleCat.of T' T') =>
      z ⊗ₜ[S'] (show (ModuleCat.extendScalars.{u, u, u} p).obj M from (1 : S') ⊗ₜ[S,p] m))
    (pushoutAlgebraIso_hom_tmul g p w h comm hp s t)

/-- **The projection formula at the two ring maps of a pushout square, on modules.** -/
theorem extendRestrictScalarsModuleIso_square
    (hp : MilnorPatching.IsPushoutSquare g p w h comm) (M : ModuleCat.{u} S) :
    (ModuleCat.extendScalars.{u, u, u} p).map ((extendRestrictScalarsModuleIso g).hom.app M) ≫
        δ (ModuleCat.extendScalars.{u, u, u} p)
            ((ModuleCat.restrictScalars g).obj (ModuleCat.of T T)) M ≫
          (pushoutAlgebraIso g p w h comm hp).hom ▷
            ((ModuleCat.extendScalars.{u, u, u} p).obj M) =
      (MilnorPatching.pushoutBaseChange g p w h comm hp).inv.app
            ((ModuleCat.extendScalars.{u, u, u} g).obj M) ≫
        (ModuleCat.restrictScalars h).map ((extendScalarsSquareIso g p w h comm).inv.app M) ≫
          (extendRestrictScalarsModuleIso h).hom.app
            ((ModuleCat.extendScalars.{u, u, u} p).obj M) := by
  apply (ModuleCat.restrictScalars p).map_injective
  apply ModuleCat.hom_ext
  refine TensorProduct.ext_threefold' (fun s t m => ?_)
  rfl

/-- The value of the projection formula over `S'`, read across the square, on the same pure
tensor: the two agree, and that is the content of
`Dualizing.extendRestrictScalarsModuleIso_square`. -/
theorem extendRestrictScalarsModuleIso_square_rhs_apply
    (hp : MilnorPatching.IsPushoutSquare g p w h comm) (M : ModuleCat.{u} S) (s : S')
    (t : (ModuleCat.restrictScalars g).obj (ModuleCat.of T T)) (m : M) :
    ((MilnorPatching.pushoutBaseChange g p w h comm hp).inv.app
            ((ModuleCat.extendScalars.{u, u, u} g).obj M) ≫
          (ModuleCat.restrictScalars h).map
              ((extendScalarsSquareIso g p w h comm).inv.app M) ≫
            (extendRestrictScalarsModuleIso h).hom.app
              ((ModuleCat.extendScalars.{u, u, u} p).obj M)) (s ⊗ₜ[S,p] (t ⊗ₜ[S] m)) =
      (show (ModuleCat.restrictScalars h).obj (ModuleCat.of T' T') from h s * w t) ⊗ₜ[S']
        (show (ModuleCat.extendScalars.{u, u, u} p).obj M from (1 : S') ⊗ₜ[S,p] m) :=
  Eq.trans
    (congrFun (congrArg (fun φ : _ ⟶ _ => (ModuleCat.Hom.hom φ).toFun)
      (extendRestrictScalarsModuleIso_square g p w h comm hp M)) _).symm
    (extendRestrictScalarsModuleIso_square_lhs_apply g p w h comm hp M s t m)


end Square

end Dualizing

end
