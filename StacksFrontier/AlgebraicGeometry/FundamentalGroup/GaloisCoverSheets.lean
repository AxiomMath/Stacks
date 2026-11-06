module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.StalksTestMaps
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleGaloisCategory
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Galois finite étale covers are étale-locally trivial torsors

Let `X` be a connected scheme and let `A` be a Galois object of the Galois category `FÉt_X` of
finite étale covers of `X`. Two `X`-morphisms `a b : W ⟶ A` from an arbitrary `X`-scheme `W`
then differ, locally on `W`, by an automorphism of `A` over `X`: every point of `W` has an open
neighbourhood on which `b = a ≫ τ` for some `τ ∈ Aut A`. If `A` is merely connected, an
automorphism of `A` is determined by its composite with any morphism from a nonempty scheme.

These are the two facts about Galois covers which descent along them consumes: together they say
that `W ×_X A` is, over `W`, the disjoint union of the graphs of the `a ≫ τ`, locally on `W`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.agreeLocus` — for an unramified morphism `f : A ⟶ X` and two
  morphisms `a b : W ⟶ A` with `a ≫ f = b ≫ f`, the open subscheme of `W` on which `a` and `b`
  agree: the preimage of the diagonal of `f`, which is an open immersion.
* `AlgebraicGeometry.galoisCategory_finiteEtaleOver` and
  `AlgebraicGeometry.fiberFunctor_finiteEtaleFiberFintypeFunctor` — the Galois category structure
  of `FÉt_X` for a connected scheme `X`, and the fibre functor of every geometric point, as
  instances.

## Main results

* `AlgebraicGeometry.Scheme.Hom.agreeLocus_ι_comp` — `a` and `b` agree on their agreement locus.
* `AlgebraicGeometry.Scheme.Hom.mem_agreeLocus_of_comp_eq` — a point lies in the agreement locus
  as soon as some morphism through which it factors equalizes `a` and `b`.
* `AlgebraicGeometry.aut_eq_of_comp_eq` — an automorphism of a connected finite étale cover is
  determined by its composite with one morphism from a nonempty scheme.
* `AlgebraicGeometry.exists_aut_mem_agreeLocus` — two morphisms into a Galois cover differ by an
  automorphism near every point.

## Implementation notes

Both results are read off a geometric point. A point `w` of `W` carries the geometric point
`W.algClosedPoint w`, whose image `x'` in `X` is a geometric point of `X`; the composites of
`W.algClosedPoint w` with `a` and `b` are elements of the geometric fibre of `A` at `x'`. The
Galois category structure does not depend on the base point, since `CategoryTheory.GaloisCategory`
is a proposition, and Galois objects are defined intrinsically, so Mathlib's transitivity and
freeness of the action of `Aut A` on the fibres of a fibre functor apply to the fibre functor at
`x'`.

## References

* [Stacks Project, Tag 0BN2](https://stacks.math.columbia.edu/tag/0BN2)
* [Stacks Project, Tag 0BNB](https://stacks.math.columbia.edu/tag/0BNB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry

/-! ### The locus where two morphisms into an unramified scheme agree -/

section AgreeLocus

variable {X W A : Scheme.{u}} (f : A ⟶ X) [FormallyUnramified f] [LocallyOfFiniteType f]
  (a b : W ⟶ A) (h : a ≫ f = b ≫ f)

/-- The open subscheme of `W` on which two morphisms `a b : W ⟶ A` with `a ≫ f = b ≫ f` agree,
for `f` unramified: the preimage of the diagonal of `f`, which is an open immersion. -/
def Scheme.Hom.agreeLocus : W.Opens :=
  ⟨(pullback.lift a b h).base ⁻¹' Set.range (pullback.diagonal f).base,
    (IsOpenImmersion.isOpen_range (pullback.diagonal f)).preimage
      (pullback.lift a b h).base.hom.continuous⟩

/-- A point lies in the agreement locus of `a` and `b` exactly when its image under
`(a, b) : W ⟶ A ×_X A` lies on the diagonal. -/
theorem Scheme.Hom.mem_agreeLocus_iff (w : W) :
    w ∈ Scheme.Hom.agreeLocus f a b h ↔
      (pullback.lift a b h).base w ∈ Set.range (pullback.diagonal f).base :=
  Iff.rfl

/-- **Two morphisms agree on their agreement locus.** -/
theorem Scheme.Hom.agreeLocus_ι_comp :
    (Scheme.Hom.agreeLocus f a b h).ι ≫ a = (Scheme.Hom.agreeLocus f a b h).ι ≫ b := by
  have hsub : Set.range ((Scheme.Hom.agreeLocus f a b h).ι ≫ pullback.lift a b h).base ⊆
      Set.range (pullback.diagonal f).base :=
    Set.range_subset_iff.mpr fun w => w.2
  have hl := IsOpenImmersion.lift_fac (pullback.diagonal f) _ hsub
  have h1 := congrArg (· ≫ pullback.fst f f) hl
  have h2 := congrArg (· ≫ pullback.snd f f) hl
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    pullback.lift_fst, pullback.lift_snd] at h1 h2
  rw [← h1, ← h2]

/-- **A point lies in the agreement locus as soon as a morphism through which it factors
equalizes the two morphisms.** -/
theorem Scheme.Hom.mem_agreeLocus_of_comp_eq {T : Scheme.{u}} (g : T ⟶ W) (hg : g ≫ a = g ≫ b)
    (t : T) : g.base t ∈ Scheme.Hom.agreeLocus f a b h := by
  have hfac : g ≫ pullback.lift a b h = (g ≫ a) ≫ pullback.diagonal f :=
    pullback.hom_ext (by simp [pullback.lift_fst]) (by simp [pullback.lift_snd, hg])
  refine ⟨(g ≫ a).base t, ?_⟩
  simpa using (congrArg (fun k => k.base t) hfac).symm

end AgreeLocus

/-! ### The Galois category of finite étale covers of a connected scheme -/

section Galois

/-- The structure morphism of a finite étale cover is étale. -/
instance etale_hom_finiteEtaleOver {X : Scheme.{u}} (A : FiniteEtaleOver X) : Etale A.hom :=
  A.prop.2

/-- The structure morphism of a finite étale cover is finite. -/
instance isFinite_hom_finiteEtaleOver {X : Scheme.{u}} (A : FiniteEtaleOver X) :
    IsFinite A.hom :=
  A.prop.1

variable {X : Scheme.{u}} [ConnectedSpace X]

/-- The finite étale covers of a connected scheme form a Galois category. The structure is
obtained from the fibre functor at any geometric point; being a proposition, it does not depend
on that choice. -/
instance galoisCategory_finiteEtaleOver : GaloisCategory (FiniteEtaleOver X) :=
  IsGaloisCategory.toGaloisCategory
    (finiteEtaleFiberFunctor (X.algClosedPoint (Classical.arbitrary X)))

/-- The geometric fibre functor at any geometric point of a connected scheme is a fibre functor of
the Galois category of its finite étale covers. -/
@[sga "1 V 3.7" "more general"]
instance fiberFunctor_finiteEtaleFiberFintypeFunctor (x : GeometricPoint X) :
    FiberFunctor (finiteEtaleFiberFintypeFunctor X x) :=
  letI : IsGaloisCategory (finiteEtaleFiberFintypeFunctor X x ⋙ FintypeCat.incl) :=
    inferInstanceAs (IsGaloisCategory (finiteEtaleFiberFunctor x))
  IsGaloisCategory.fiberFunctor (finiteEtaleFiberFintypeFunctor X x)

/-- The element of the geometric fibre of a finite étale cover `A` at the geometric point
`W.algClosedPoint w ≫ p` given by a morphism `c : W ⟶ A` over `p`. -/
def fiberPointOfComp {W : Scheme.{u}} (w : W) {A : FiniteEtaleOver X} (c : W ⟶ A.left) :
    (finiteEtaleFiberFintypeFunctor X ((W.algClosedPoint w).map (c ≫ A.hom))).obj A :=
  (⟨(W.algClosedPoint w).hom ≫ c, Category.assoc _ _ _⟩ :
    finiteEtaleFiber ((W.algClosedPoint w).map (c ≫ A.hom)) A)

/-- Automorphisms of a finite étale cover act on fibre points of the form `fiberPointOfComp` by
composition. -/
theorem finiteEtaleFiberFintypeFunctor_map_fiberPointOfComp {W : Scheme.{u}} (w : W)
    {A : FiniteEtaleOver X} (c : W ⟶ A.left) (τ : A ⟶ A) :
    ((finiteEtaleFiberFintypeFunctor X ((W.algClosedPoint w).map (c ≫ A.hom))).map τ
        (fiberPointOfComp w c)).1 = (W.algClosedPoint w).hom ≫ c ≫ τ.left :=
  Category.assoc _ _ _

/-- **An automorphism of a connected finite étale cover is determined by one composite.** If `A`
is connected, `V` is a nonempty scheme and `c : V ⟶ A` satisfies `c ≫ τ = c ≫ τ'` for two
automorphisms of `A` over `X`, then `τ = τ'`: the element of the geometric fibre given by `c` at
a geometric point of `V` is fixed by `τ⁻¹ τ'`, and `Aut A` acts freely on the fibres of a
connected object. -/
theorem aut_eq_of_comp_eq {A : FiniteEtaleOver X} [IsConnected A] {V : Scheme.{u}} [Nonempty V]
    (c : V ⟶ A.left) {τ τ' : Aut A} (h : c ≫ τ.asIso.hom.left = c ≫ τ'.asIso.hom.left) : τ = τ' := by
  let v : V := Classical.arbitrary V
  let x' := (V.algClosedPoint v).map (c ≫ A.hom)
  refine evaluation_aut_injective_of_isConnected (finiteEtaleFiberFintypeFunctor X x') A
    (fiberPointOfComp v c) ?_
  apply Subtype.ext
  change ((finiteEtaleFiberFintypeFunctor X x').map τ.asIso.hom (fiberPointOfComp v c)).1 =
    ((finiteEtaleFiberFintypeFunctor X x').map τ'.asIso.hom (fiberPointOfComp v c)).1
  rw [finiteEtaleFiberFintypeFunctor_map_fiberPointOfComp,
    finiteEtaleFiberFintypeFunctor_map_fiberPointOfComp, h]

/-- **Two morphisms into a Galois cover differ by an automorphism near every point.** Let `A` be
a Galois object of `FÉt_X` and let `a b : W ⟶ A` be morphisms with `a ≫ A.hom = b ≫ A.hom`. Every
point `w` of `W` lies in the agreement locus of `a ≫ τ` and `b` for some automorphism `τ` of `A`:
at the geometric point of `W` at `w`, the composites with `a` and `b` are two elements of one
geometric fibre of `A`, on which `Aut A` acts transitively. -/
theorem exists_aut_mem_agreeLocus {A : FiniteEtaleOver X} [IsGalois A] {W : Scheme.{u}}
    (a b : W ⟶ A.left) (hab : a ≫ A.hom = b ≫ A.hom) (w : W) :
    ∃ (τ : Aut A) (h : (a ≫ τ.asIso.hom.left) ≫ A.hom = b ≫ A.hom),
      w ∈ Scheme.Hom.agreeLocus A.hom (a ≫ τ.asIso.hom.left) b h := by
  let x' := (W.algClosedPoint w).map (a ≫ A.hom)
  let F := finiteEtaleFiberFintypeFunctor X x'
  let ea : F.obj A := fiberPointOfComp w a
  let eb : F.obj A := (⟨(W.algClosedPoint w).hom ≫ b, by
      rw [Category.assoc, ← hab]
      rfl⟩ : finiteEtaleFiber x' A)
  obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq (Aut A) ea eb
  have hτ' : (W.algClosedPoint w).hom ≫ a ≫ τ.asIso.hom.left = (W.algClosedPoint w).hom ≫ b := by
    rw [← finiteEtaleFiberFintypeFunctor_map_fiberPointOfComp]
    exact congrArg Subtype.val hτ
  have hw : (a ≫ τ.asIso.hom.left) ≫ A.hom = b ≫ A.hom := by
    rw [Category.assoc, MorphismProperty.Over.w, hab]
  refine ⟨τ, hw, ?_⟩
  rw [← Scheme.algClosedPointHom_apply W w default]
  exact Scheme.Hom.mem_agreeLocus_of_comp_eq A.hom _ _ hw _ hτ' _

end Galois

end AlgebraicGeometry

end
