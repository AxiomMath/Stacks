module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandNoSliceSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualLocalDualBasis
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrict
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.CategoryTheory.Monoidal.RigidAdjunction

/-!
# The dual of an invertible sheaf of modules on a ringed site

Let `(C, 𝒪)` be a ringed site and let `L` be an *invertible* sheaf of `𝒪`-modules, i.e. one for
which tensoring by `L` is an equivalence of the category of sheaves of `𝒪`-modules. This file
proves the second part of [Stacks, Tag 040A](https://stacks.math.columbia.edu/tag/040A) — and
therewith the second part of [Stacks, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT),
which is the same statement for a ringed space: the evaluation pairing

`ε : SheafHom(L, 𝒪) ⊗_𝒪 L ⟶ 𝒪`

is an isomorphism, and the dual `L^∨ = SheafHom(L, 𝒪)` is again invertible.

The two clauses are one statement: an isomorphism `L^∨ ⊗_𝒪 L ≅ 𝒪` is a trivializing pairing, and
[Stacks, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K) (2) ⟹ (1) turns a trivializing
pairing into invertibility of either factor. So everything rests on the evaluation clause, which
is proved in three steps, all but the last of them already in the library.

* An invertible sheaf of modules is, on a covering family of every object, a direct summand of a
  finite free sheaf of modules. This is Tag 0B8N (b),
  `Stacks.SheafOfModules.exists_cover_isDirectSummand_finiteFree`.
* That is the local hypothesis of [Stacks, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV),
  so `Stacks.SheafOfModules.exactPairingDualSheafOfRetract` applies and exhibits `L^∨` as a
  **left dual** of `L`, with the canonical evaluation `ε` as the evaluation of the exact pairing.
* In an arbitrary monoidal category the evaluation of an exact pairing on `X` and `Y` is an
  isomorphism as soon as `tensorRight X` is an equivalence
  (`CategoryTheory.ExactPairing.isIso_evaluation`), and for an invertible sheaf of modules
  tensoring is an equivalence by definition.

## Main definitions

* `Stacks.SheafOfModules.piUnitIsoFree` and `Stacks.SheafOfModules.retractFreeOfIsSplitMono`:
  a finite product of copies of the structure sheaf is the free sheaf of modules on a finite
  index type, so a split monomorphism into such a product is a retract onto a finite free sheaf
  of modules. This converts the conclusion of Tag 0B8N (b) into the hypothesis of Tag 0FNV.
* `Stacks.SheafOfModules.InvertibleSummandIndex`, with `invertibleSummandObj`,
  `invertibleSummandRank` and `invertibleSummandRetract`: the canonical covering family attached
  to an invertible sheaf of modules, namely the pairs `(V, n)` of an object and a rank such that
  `L|_V` is a retract of the free sheaf of modules on `n` generators.
* `Stacks.SheafOfModules.exactPairingDualSheafOfIsInvertible`: **the dual of an invertible sheaf
  of modules is a left dual of it**, i.e. Tag 0FNV applies to every invertible sheaf of modules.

## Main results

* `Stacks.SheafOfModules.coversTop_invertibleSummandObj`: the objects carrying a finite free
  splitting of an invertible sheaf of modules cover the final object of the site.
* `Stacks.SheafOfModules.Invertible.isIso_evaluation` and
  `Stacks.SheafOfModules.Invertible.isIso_tensorSheafBraiding_hom_comp_evaluation`: **Tag 040A
  (2) and Tag 01CT (2), the evaluation clause**, in the order of Tag 0FNV and in the order the
  tags write it.
* `Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf`: **Tag 040A (2) and Tag 01CT (2),
  the invertibility clause.**

## Implementation notes

**Why the covering family is indexed by pairs, and not chosen.** Tag 0B8N (b) produces, for each
object `U` separately, a covering family of `U` whose members carry a splitting, whereas Tag 0FNV
consumes a single family of objects covering the final object
(`CategoryTheory.GrothendieckTopology.CoversTop`). The passage needs no choice and no refinement
of sieves: take as index type *all* pairs `(V, n)` for which a splitting exists. A covering family
of `U` then consists of objects which are themselves members of that family, and
`CategoryTheory.Sieve.ofArrows_le_ofObjects` together with
`CategoryTheory.Sieve.ofObjects_mono` is the whole proof. In particular the per-object predicate
`Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree` is *not* used: it asks for a splitting
over every member of a covering **sieve**, which would additionally require that a splitting
restricts along an arbitrary morphism of the site.

**Products versus coproducts.** Tag 0B8N (b) splits `L|_V` off a finite *product* of copies of
the structure sheaf, while `SheafOfModules.free` is by definition a *coproduct*. For a finite
index type the two agree, because sheaves of modules form a preadditive category with finite
products: that is `CategoryTheory.Limits.HasBiproduct.of_hasProduct`, and `piUnitIsoFree` is the
resulting comparison, composed with the reindexing `Fin n ≃ ULift (Fin n)` which puts the index
type in the module universe that `SheafOfModules.free` requires.

**Which monoidal structure.** The exact pairing is taken in
`Stacks.SheafOfModules.Strict.monoidalCategory`, whose tensor product *is* the tensor product
sheaf of Tag 01CA and whose unit *is* `SheafOfModules.unit`, both on the nose; this is what makes
the evaluation of the exact pairing be `Stacks.SheafOfModules.evaluation` itself rather than a
conjugate of it. Invertibility in the sense of Tag 01CS supplies a tensor inverse
(`Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit`, Tag 0B8K), and
`CategoryTheory.MonoidalCategory.HasInverse.ofBraided` makes it two-sided using the braiding of
the strict structure, which is what `tensorRight L` being an equivalence needs.

**This superseded a hypothesis.** `Stacks.SheafOfModules.isIso_evaluation_of_isInvertible` of
`StacksFrontier/AlgebraicGeometry/InvertibleDual/Evaluation.lean` used to prove the evaluation
clause only on a ringed space all of whose structure-sheaf stalks are local rings, because the
route taken there went through the converse half of Tag 0B8M. The route here needs no hypothesis
on the stalks and no local triviality at all, only Tag 0B8N (b), which is exactly what the
Stacks source says the proof of Tag 040A (2) is ("part (2) follows from Lemma 0B8N and its
proof"); that declaration and
`Stacks.SheafOfModules.Scheme.isIso_evaluation_of_isInvertible` are now this one read on the
site of opens, with the hypothesis dropped.

**Why these declarations carry Tag 01CT as well.** Tag 01CT is Tag 040A for a ringed space,
whose opens with the open-cover topology form a ringed site, so clause (2) of the two tags is
one statement proved once here, exactly as clause (1) of the two is proved once in
`Stacks.SheafOfModules.tensorProduct_isInvertible`.

**Universes.** The sections of `𝒪` and of the modules live in `max u v`, where `u` and `v` are
the universes of the objects and the arrows of the site. That is forced by the internal hom of
Tag 03EM, of which the dual sheaf is an instance: a section of `SheafHom(L, 𝒪)` over `U` is a
morphism of presheaves of modules on the slice site `C/U`, whose arrows live in `max u v`. The
two auxiliary constructions above are stated for an arbitrary site and an arbitrary module
universe, which is where they belong.

## References

* [Stacks Project, Tag 040A](https://stacks.math.columbia.edu/tag/040A)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT) — Tag 040A for a ringed
  space.
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N) — an invertible module is
  locally a direct summand of a finite free module.
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K) — invertibility from a
  trivializing pairing.
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV) — the dual of a module
  locally a finite free summand is a left dual.
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP) — left duals in a
  monoidal category.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the monoidal structure.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace Stacks.SheafOfModules

section FiniteFree

universe t v₁ u₁

variable {D : Type u₁} [Category.{v₁} D] {K : GrothendieckTopology D}
  [HasWeakSheafify K AddCommGrpCat.{t}] [K.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- **A finite product of copies of the structure sheaf is a finite free sheaf of modules.**
Sheaves of modules form a preadditive category with finite products, so a finite product of
copies of `SheafOfModules.unit` is also their coproduct, which is `SheafOfModules.free`; the
index type is reindexed along `Fin n ≃ ULift (Fin n)` to put it in the module universe. -/
noncomputable def piUnitIsoFree (R : Sheaf K RingCat.{t}) (n : ℕ) :
    (∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit R) ≅
      SheafOfModules.free (R := R) (ULift.{t} (Fin n)) :=
  have := HasBiproduct.of_hasProduct (fun _ : ULift.{t} (Fin n) ↦ SheafOfModules.unit R)
  Pi.whiskerEquiv (f := fun _ : Fin n ↦ SheafOfModules.unit R)
      (g := fun _ : ULift.{t} (Fin n) ↦ SheafOfModules.unit R)
      Equiv.ulift.symm (fun _ ↦ Iso.refl _) ≪≫
    (biproduct.isoProduct _).symm ≪≫ biproduct.isoCoproduct _

/-- **A split monomorphism into a finite product of copies of the structure sheaf is a retract
onto a finite free sheaf of modules.** This is the form of the local hypothesis that the duality
statements of Tag 0FNV consume, obtained from the form Tag 0B8N (b) produces. -/
noncomputable def retractFreeOfIsSplitMono {R : Sheaf K RingCat.{t}}
    {M : SheafOfModules.{t} R} {n : ℕ}
    (s : M ⟶ ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit R) [IsSplitMono s] :
    Retract M (SheafOfModules.free (R := R) (ULift.{t} (Fin n))) where
  i := s ≫ (piUnitIsoFree R n).hom
  r := (piUnitIsoFree R n).inv ≫ retraction s
  retract := by
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact IsSplitMono.id s

end FiniteFree

section RingedSite

universe v u

attribute [local instance] Strict.monoidalCategory Strict.braidedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (L : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪))

/-- **The canonical index type of the finite free splittings of a sheaf of modules**: the pairs
`(V, n)` of an object of the site and a rank such that `L|_V` is a retract of the free sheaf of
`𝒪|_V`-modules on `n` generators. No choice is involved — every such pair is an index — and by
`Stacks.SheafOfModules.coversTop_invertibleSummandObj` the objects occurring in it cover the
final object as soon as `L` is invertible. -/
def InvertibleSummandIndex : Type u :=
  {p : C × ℕ // Nonempty (Retract (L.over p.1)
    (SheafOfModules.free (R := (TensorSheafification.structureSheaf 𝒪 h𝒪).over p.1)
      (ULift.{max u v} (Fin p.2))))}

variable {𝒪 h𝒪 L}

/-- The object of the site on which a member of `Stacks.SheafOfModules.InvertibleSummandIndex`
splits `L`. -/
def invertibleSummandObj (k : InvertibleSummandIndex 𝒪 h𝒪 L) : C := k.1.1

/-- The rank of the free sheaf of modules onto which a member of
`Stacks.SheafOfModules.InvertibleSummandIndex` splits `L`. -/
def invertibleSummandRank (k : InvertibleSummandIndex 𝒪 h𝒪 L) : ℕ := k.1.2

/-- A splitting of `L|_V` onto a finite free sheaf of modules, for a member of
`Stacks.SheafOfModules.InvertibleSummandIndex`. This is the one place where the `Nonempty` of the
index type is turned into data. -/
noncomputable def invertibleSummandRetract (k : InvertibleSummandIndex 𝒪 h𝒪 L) :
    Retract (L.over (invertibleSummandObj k))
      (SheafOfModules.free
        (R := (TensorSheafification.structureSheaf 𝒪 h𝒪).over (invertibleSummandObj k))
        (ULift.{max u v} (Fin (invertibleSummandRank k)))) :=
  k.2.some

variable (𝒪 h𝒪 L)

/-- **The objects carrying a finite free splitting of an invertible sheaf of modules cover the
final object of the site.** By Tag 0B8N (b) every object `U` has a covering family whose members
carry such a splitting; the members of that family are themselves members of the global family,
through the identity, so the covering sieve it generates is contained in the sieve of objects of
the global family. No pullback of sieves and no refinement is needed. -/
theorem coversTop_invertibleSummandObj [IsInvertible 𝒪 h𝒪 L] :
    J.CoversTop (invertibleSummandObj (𝒪 := 𝒪) (h𝒪 := h𝒪) (L := L)) := by
  intro W
  obtain ⟨I, V, f, hcov, hret⟩ := exists_cover_isDirectSummand_finiteFree h𝒪 L W
  refine J.superset_covering ((Sieve.ofArrows_le_ofObjects V f).trans
    (Sieve.ofObjects_mono ?_)) hcov
  rintro _ ⟨i, rfl⟩
  obtain ⟨n, s, hs⟩ := hret i
  exact ⟨⟨(V i, n), ⟨retractFreeOfIsSplitMono s⟩⟩, rfl⟩

/-- **The dual of an invertible sheaf of modules is a left dual of it.** An invertible sheaf of
modules is locally a direct summand of a finite free sheaf of modules by Tag 0B8N (b), which is
the local hypothesis of Tag 0FNV, so the dual `L^∨ = SheafHom(L, 𝒪)`, with the canonical
coevaluation `𝒪 ⟶ L ⊗ L^∨` and the canonical evaluation `ε : L^∨ ⊗ L ⟶ 𝒪`, satisfies the two
triangle identities. -/
@[instance_reducible]
noncomputable def exactPairingDualSheafOfIsInvertible [IsInvertible 𝒪 h𝒪 L] :
    ExactPairing L (dualSheaf 𝒪 h𝒪 L) :=
  exactPairingDualSheafOfRetract 𝒪 h𝒪 L (coversTop_invertibleSummandObj 𝒪 h𝒪 L)
    (I := fun k ↦ ULift.{max u v} (Fin (invertibleSummandRank k))) invertibleSummandRetract

namespace Invertible

/-- **Stacks Project, Tag 040A (2), the evaluation clause.** For an invertible sheaf of
`𝒪`-modules `L` on a ringed site the evaluation pairing `SheafHom(L, 𝒪) ⊗_𝒪 L ⟶ 𝒪` is an
isomorphism.

The dual is a left dual of `L` by `exactPairingDualSheafOfIsInvertible`, and the evaluation of an
exact pairing is an isomorphism whenever tensoring on the right by the first object is an
equivalence, which for an invertible sheaf of modules it is.

A ringed space is a ringed site, so this is also the evaluation clause of Tag 01CT (2); see
`Stacks.SheafOfModules.isIso_evaluation_of_isInvertible` for that reading. -/
@[stacks 01CT "evaluation", stacks 040A "part (2)", ega "0 5.4.3" "more general"]
theorem isIso_evaluation [IsInvertible 𝒪 h𝒪 L] : IsIso (evaluation 𝒪 h𝒪 L) := by
  obtain ⟨N, ⟨e⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit L).mp ‹IsInvertible 𝒪 h𝒪 L›
  have e' : L ⊗ N ≅
      𝟙_ (SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) := e
  have hequiv : (MonoidalCategory.tensorRight L).IsEquivalence :=
    (MonoidalCategory.HasInverse.ofBraided e').tensorRightEquivalence.isEquivalence_functor
  exact @ExactPairing.isIso_evaluation _ _ _ L (dualSheaf 𝒪 h𝒪 L)
    (exactPairingDualSheafOfIsInvertible 𝒪 h𝒪 L) hequiv

/-- **Stacks Project, Tag 040A (2) and Tag 01CT (2), the evaluation clause in the order the tags
write it.** The evaluation map `L ⊗_𝒪 SheafHom(L, 𝒪) ⟶ 𝒪` is an isomorphism. It is the canonical
pairing of `Stacks.SheafOfModules.evaluation`, whose factors come in the order Tag 0FNV writes
them, preceded by the braiding of the tensor product sheaf, which is what exchanges the two
factors; in this order it is the trivializing pairing identifying `L^∨` as a tensor inverse of
`L`. -/
@[stacks 01CT "evaluation", stacks 040A "part (2)", ega "0 5.4.3" "more general"]
theorem isIso_tensorSheafBraiding_hom_comp_evaluation [IsInvertible 𝒪 h𝒪 L] :
    IsIso ((tensorSheafBraiding 𝒪 h𝒪 L (dualSheaf 𝒪 h𝒪 L)).hom ≫ evaluation 𝒪 h𝒪 L) := by
  let := isIso_evaluation 𝒪 h𝒪 L
  exact Iso.isIso_hom
    (tensorSheafBraiding 𝒪 h𝒪 L (dualSheaf 𝒪 h𝒪 L) ≪≫ asIso (evaluation 𝒪 h𝒪 L))

/-- **Stacks Project, Tag 040A (2) and Tag 01CT (2), the invertibility clause.** The dual
`L^∨ = SheafHom(L, 𝒪)` of an invertible sheaf of `𝒪`-modules is again invertible: the evaluation
pairing is an isomorphism `L^∨ ⊗_𝒪 L ≅ 𝒪`, which is Tag 0B8K (2) for `L^∨`. -/
@[stacks 01CT "dual_invertible", stacks 040A "part (2)"]
theorem isInvertible_dualSheaf [IsInvertible 𝒪 h𝒪 L] :
    IsInvertible 𝒪 h𝒪 (dualSheaf 𝒪 h𝒪 L) := by
  have := isIso_evaluation 𝒪 h𝒪 L
  have e : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj
        ((dualSheaf 𝒪 h𝒪 L))).obj (L)) ≅
      SheafOfModules.unit (TensorSheafification.structureSheaf 𝒪 h𝒪) :=
    asIso (evaluation 𝒪 h𝒪 L)
  exact (isInvertible_iff_exists_tensor_iso_unit (dualSheaf 𝒪 h𝒪 L)).mpr ⟨L, ⟨e⟩⟩

/-- **Stacks Project, Tag 0B8N (c).** A sheaf of `𝒪`-modules `N` whose tensor product with `L` is
isomorphic to the structure sheaf is isomorphic to `SheafHom(L, 𝒪)`.

The hypothesis is clause (2) of the tag, so `L` is invertible and the evaluation pairing
`SheafHom(L, 𝒪) ⊗_𝒪 L ⟶ 𝒪` is an isomorphism by `isIso_evaluation`. That exhibits
`SheafHom(L, 𝒪)` as a two-sided tensor inverse of `L`, the braiding supplying the other order,
while the given isomorphism exhibits `N` as one; a two-sided tensor inverse in a monoidal
category is unique up to isomorphism
(`CategoryTheory.MonoidalCategory.HasInverse.inv_iso`). -/
@[stacks 0B8N "(c)", stacks 0B8K "the tensor inverse is the dual", sga "6 VIII 3.5" "partial"]
noncomputable def tensorInverseIsoDualSheaf
    (N : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪))
    (e : ((Tensor.sheafTensor
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj L).obj N ≅
      SheafOfModules.unit (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    N ≅ dualSheaf 𝒪 h𝒪 L := by
  have e' : L ⊗ N ≅
      𝟙_ (SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) := e
  haveI : IsInvertible 𝒪 h𝒪 L := (isInvertible_iff_exists_tensor_iso_unit L).mpr ⟨N, ⟨e⟩⟩
  have hev : dualSheaf 𝒪 h𝒪 L ⊗ L ≅
      𝟙_ (SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :=
    @asIso _ _ _ _ (evaluation 𝒪 h𝒪 L) (isIso_evaluation 𝒪 h𝒪 L)
  exact MonoidalCategory.HasInverse.inv_iso (MonoidalCategory.HasInverse.ofBraided e')
    { inv := dualSheaf 𝒪 h𝒪 L
      isoLeft := β_ L (dualSheaf 𝒪 h𝒪 L) ≪≫ hev
      isoRight := hev }

end Invertible

end RingedSite

end Stacks.SheafOfModules

end
