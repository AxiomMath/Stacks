module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafUnitSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor

/-!
# A local section of a monoidal tensor product of sheaves of modules is a finite sum of pure
tensors

Let `(X, 𝒪_X)` be a ringed space and let `F`, `G` be sheaves of `𝒪_X`-modules. The tensor product
sheaf `F ⊗_{𝒪_X} G` of Tag 01CA is the sheafification of `U ↦ F(U) ⊗_{𝒪_X(U)} G(U)`, so a section
of it is only *locally* a finite sum of pure tensors; that statement is
`Stacks.SheafOfModules.TensorUnit.exists_sieve_sum_toTensorSheafSection`, proved at the Tag 01CA
spelling `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`.

This file makes that available where it is consumed: at the **monoidal** tensor product of
`SheafOfModules.monoidalCategorySheafTensor`, the structure on `Mod 𝒪_X` whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor` and on which the derived tensor product of Tag 0FPB is
built, and in the **neighbourhood** rather than the sieve form, which is the shape a shrinking
argument consumes.

## Main results

* `Stacks.SheafOfModules.TensorUnit.monoidalTensorObj_eq_tensorSheaf`: the identification
  `F ⊗ G = Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf X F G`, which is `rfl`. It is
  stated once here and everything else in the file is read through it.
* `Stacks.SheafOfModules.TensorUnit.monoidalTensorUnit_eq_unit`: the companion identification
  `𝟙_ (Mod 𝒪_X) = SheafOfModules.unit`, also `rfl`.
* `Stacks.SheafOfModules.TensorUnit.exists_sieve_sum_monoidalTensorSection`: the sieve form of the
  pure-tensor expression, restated at the monoidal tensor product.
* `Stacks.SheafOfModules.TensorUnit.exists_nhd_sum_monoidalTensorSection`: **the neighbourhood
  form.** Every point of `U` has an open neighbourhood `V ≤ U` on which the restriction of a given
  section of `F ⊗ G` is `∑ j, a j ⊗ b j` for finitely many sections `a j` of `F` and `b j` of `G`
  over `V`.

## Implementation notes

**Why the identification is paid once.** `F ⊗ G`, `(Stacks.SheafOfModules.Tensor.sheafTensor
X.sheaf).obj F |>.obj G` and `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf X F G` are
one term: the monoidal structure of `SheafOfModules.monoidalCategorySheafTensor` is a re-seating
whose tensor product is `sheafTensor` on the nose, and `sheafTensor` is the sheafification of the
objectwise tensor product, which is what `tensorSheaf` is. So no transport is needed anywhere, and
the sections map `Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection` already lands
in `(F ⊗ G).val.obj U`. Recording that as a single `rfl` lemma, rather than letting each statement
below re-derive it, keeps every declaration here at zero spelling crossings.

The monoidal structure is an `@[instance_reducible]` definition rather than an instance, so it is
introduced with `letI`; it is *not* the structure of
`Stacks.SheafOfModules.monoidalCategory`, which localizes sheafification directly and is **not**
definitionally equal to the re-seated one (checked). The re-seated one is the structure the
complex- and derived-level tensor products of this development rest on, which is why the
statements below are at it.

**Sieve versus neighbourhood.** For the open-cover topology, membership of a sieve in
`Opens.grothendieckTopology` unfolds to `∀ x ∈ U, ∃ V (f : V ⟶ U), S f ∧ x ∈ V`, so the passage
from the sieve form to the neighbourhood form is immediate. It is recorded separately because the
two shapes are not interchangeable to a consumer: a shrinking argument asks for a neighbourhood of
a given point, and elsewhere in this development the absence of exactly this passage has been
recorded as a gap.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB) — the derived tensor
  product, which rests on the monoidal structure used here.
-/

@[expose] public section

open CategoryTheory MonoidalCategory TensorProduct TopologicalSpace Opposite

universe u

noncomputable section

namespace Stacks.SheafOfModules.TensorUnit

/-- The monoidal structure on `Mod 𝒪_X` whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor`, pinned at a ringed space.

`SheafOfModules.monoidalCategorySheafTensor` ties the universe of the sections to the universes of
the site as `max u v`, which does not solve against the diagonal `u` of a ringed space while those
universes are still metavariables; declaring it by name at `Y.sheaf`, as here, is what makes
instance search find it. -/
local instance monoidalModOfRingedSpace (Y : AlgebraicGeometry.RingedSpace.{u, u}) :
    MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) :=
  SheafOfModules.monoidalCategorySheafTensor Y.sheaf

variable (X : AlgebraicGeometry.RingedSpace.{u, u})
  (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))

/-- **The tensor product of the monoidal structure on `Mod 𝒪_X` is the tensor product sheaf of
Tag 01CA.** Both are the sheafification of `U ↦ F(U) ⊗_{𝒪_X(U)} G(U)`: the monoidal structure of
`SheafOfModules.monoidalCategorySheafTensor` is a re-seating whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor`, and that is the sheafification of the objectwise
tensor product.

This is the one identification the rest of this file is read through. -/
public theorem monoidalTensorObj_eq_tensorSheaf :
    F ⊗ G =
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj
        (G)) :=
    rfl

/-- The unit of the monoidal structure on `Mod 𝒪_X` is the structure sheaf read as a module over
itself, not merely isomorphic to it. -/
public theorem monoidalTensorUnit_eq_unit :
    (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
      = SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) := rfl

/-- **A section of the monoidal tensor product is, on a covering sieve, a finite sum of pure
tensors.** This is `exists_sieve_sum_toTensorSheafSection` read at `F ⊗ G`; no transport is
involved, the two objects being one term by `monoidalTensorObj_eq_tensorSheaf`. -/
public theorem exists_sieve_sum_monoidalTensorSection (U : Opens X.carrier)
    (t : (F ⊗ G).val.obj (op U)) :
    ∃ S : Sieve U, S ∈ Stacks.SheafOfModules.TensorStalkRingedSpace.JX X U ∧
      ∀ ⦃V : Opens X.carrier⦄ (k : V ⟶ U), S.arrows k →
        ∃ (n : ℕ) (a : Fin n → F.val.obj (op V)) (b : Fin n → G.val.obj (op V)),
          (F ⊗ G).val.map k.op t =
            ∑ j, Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G (op V)
              (a j ⊗ₜ[X.presheaf.obj (op V)] b j) :=
  exists_sieve_sum_toTensorSheafSection X F G U t

/-- **A section of the monoidal tensor product is a finite sum of pure tensors on a neighbourhood
of each point.** Given a section `t` of `F ⊗_{𝒪_X} G` over an open `U` and a point `x ∈ U`, there
is an open `V` with `x ∈ V ≤ U` and finitely many sections `a j` of `F` and `b j` of `G` over `V`
with `t|_V = ∑ j, a j ⊗ b j`.

This is the shape a shrinking argument consumes: the sieve of
`exists_sieve_sum_monoidalTensorSection` is a member of the open-cover topology, whose membership
is by definition the existence of such a `V` at every point. -/
public theorem exists_nhd_sum_monoidalTensorSection (U : Opens X.carrier)
    (t : (F ⊗ G).val.obj (op U)) (x : X.carrier) (hx : x ∈ U) :
    ∃ (V : Opens X.carrier) (hVU : V ≤ U), x ∈ V ∧
      ∃ (n : ℕ) (a : Fin n → F.val.obj (op V)) (b : Fin n → G.val.obj (op V)),
        (F ⊗ G).val.map (homOfLE hVU).op t =
          ∑ j, Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G (op V)
            (a j ⊗ₜ[X.presheaf.obj (op V)] b j) := by
  obtain ⟨S, hS, hsum⟩ := exists_sieve_sum_monoidalTensorSection X F G U t
  obtain ⟨V, k, hk, hxV⟩ := (Opens.mem_grothendieckTopology _).mp hS x hx
  obtain ⟨n, a, b, hab⟩ := hsum k hk
  exact ⟨V, leOfHom k, hxV, n, a, b, by rwa [Subsingleton.elim (homOfLE (leOfHom k)) k]⟩

end Stacks.SheafOfModules.TensorUnit

end

end
