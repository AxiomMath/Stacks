module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteGSetCover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Galois cover realizing an open normal subgroup of the étale fundamental group

Let `X` be a connected scheme with a geometric point `x` and let `V` be an *open normal* subgroup
of `π₁(X, x)`. `AlgebraicGeometry.exists_stabilizer_eq_of_isOpen` already produces a finite étale
cover of `X` with a point of its geometric fibre whose stabilizer is `V`. This file records what
normality of `V` adds: the cover produced from the coset space `π₁(X, x)/V` is a *Galois* object
of `FÉt_X`, and its degree is the index `[π₁(X, x) : V]`.

The cover is the one attached to the finite continuous `π₁(X, x)`-set `π₁(X, x)/V` by
`AlgebraicGeometry.exists_finiteEtaleOver_fiber_equiv`. Two things come out of normality.

* The right translations of `π₁(X, x)/V` are `π₁(X, x)`-equivariant — this is exactly associativity
  once the left action is written as multiplication by a coset, which needs `V` normal for
  `π₁(X, x)/V` to be a group. Each of them is therefore induced by an endomorphism of the cover
  (`AlgebraicGeometry.exists_hom_of_equivariant`), and the translations by `q` and `q⁻¹` are
  mutually inverse because the geometric fibre functor is faithful. So `Aut` of the cover acts
  transitively on its geometric fibre.
* The action of `π₁(X, x)` on `π₁(X, x)/V` is transitive, so the total space of the cover is
  connected.

A connected object whose automorphism group acts transitively on one geometric fibre is a Galois
object, which is `CategoryTheory.PreGaloisCategory.isGalois_iff_pretransitive`.

This is the half of the dictionary between open subgroups of `π₁` and finite étale covers which a
*degree* condition on covers has to pass through: a condition on the index of `V` becomes a
condition on the degree of the cover, and vice versa.

## Main results

* `AlgebraicGeometry.exists_isGalois_card_fiber_eq_index_stabilizer_eq_of_isOpen` — an open normal
  subgroup `V` of `π₁(X, x)` is the stabilizer of a point of the geometric fibre of a Galois
  finite étale cover of `X` of degree `[π₁(X, x) : V]`.

## References

* [Stacks Project, Tag 03VF](https://stacks.math.columbia.edu/tag/03VF)
* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry

/-! ### The left action on a coset space of a normal subgroup is multiplication -/

/-- For a normal subgroup `V ≤ G` the left action of `G` on the coset space is multiplication by
the coset of the acting element, the coset space being a group. -/
theorem smul_quotient_eq_mul {G : Type*} [Group G] (V : Subgroup G) [V.Normal] (σ : G)
    (z : G ⧸ V) : σ • z = (QuotientGroup.mk σ : G ⧸ V) * z := by
  induction z using QuotientGroup.induction_on with | H g => rfl

namespace EtaleFundamentalGroup

variable {X : Scheme.{u}} [ConnectedSpace X] (x : GeometricPoint X)

/-- The action of the automorphism group of a finite étale cover on its geometric fibre is the
functorial action of the geometric fibre functor; the `FintypeCat`-valued and `Type`-valued fibre
functors agree on the nose. -/
theorem autMulFiber_smul_eq (Y : FiniteEtaleOver X) (φ : Aut Y)
    (y : ((finiteEtaleFiberFintypeFunctor X x).obj Y).obj) :
    φ • y = (finiteEtaleFiberFunctor x).map φ.hom y :=
  rfl

/-- Transitivity of the automorphism group of a finite étale cover on its geometric fibre,
transported from the `Type`-valued geometric fibre functor to the `FintypeCat`-valued one in which
`CategoryTheory.PreGaloisCategory.isGalois_iff_pretransitive` states it. -/
theorem isPretransitive_aut_of_forall_exists_map_eq (Y : FiniteEtaleOver X)
    (h : ∀ a b : (finiteEtaleFiberFunctor x).obj Y,
      ∃ φ : Aut Y, (finiteEtaleFiberFunctor x).map φ.hom a = b) :
    MulAction.IsPretransitive (Aut Y) ((finiteEtaleFiberFintypeFunctor X x).obj Y) :=
  ⟨fun a b ↦ (h a b).imp fun φ hφ ↦ (autMulFiber_smul_eq x Y φ a).trans hφ⟩

/-! ### Right translations as automorphisms of the cover -/

/-- **Right translation of a coset space is realized by an automorphism of the cover.** Let `V` be
a normal subgroup of `π₁(X, x)`, let `Y` be a finite étale cover of `X` and let
`e : F_x(Y) ≃ π₁(X, x)/V` be an equivariant bijection. Every element `q` of `π₁(X, x)/V` gives an
automorphism of `Y` acting on the geometric fibre by `y ↦ e⁻¹(e y · q)`.

Right translation is equivariant because the left action is multiplication by a coset
(`AlgebraicGeometry.smul_quotient_eq_mul`), so the two multiplications associate; an equivariant
self-map of a geometric fibre comes from an endomorphism of the cover, and the endomorphisms
attached to `q` and `q⁻¹` compose to the identity on the fibre, hence are mutually inverse because
the geometric fibre functor is faithful. -/
theorem exists_aut_map_eq_mul_of_fiberEquiv (V : Subgroup (EtaleFundamentalGroup X x)) [V.Normal]
    (Y : FiniteEtaleOver X)
    (e : (finiteEtaleFiberFunctor x).obj Y ≃ EtaleFundamentalGroup X x ⧸ V)
    (he : ∀ (σ : EtaleFundamentalGroup X x) y, e (σ • y) = σ • e y)
    (q : EtaleFundamentalGroup X x ⧸ V) :
    ∃ φ : Aut Y, ∀ y, (finiteEtaleFiberFunctor x).map φ.hom y = e.symm (e y * q) := by
  have key : ∀ r : EtaleFundamentalGroup X x ⧸ V, ∃ g : Y ⟶ Y,
      ∀ y, (finiteEtaleFiberFunctor x).map g y = e.symm (e y * r) := by
    intro r
    refine exists_hom_of_equivariant x (fun y ↦ e.symm (e y * r)) fun σ y ↦ ?_
    apply e.injective
    rw [he, Equiv.apply_symm_apply, he, Equiv.apply_symm_apply, smul_quotient_eq_mul,
      smul_quotient_eq_mul, mul_assoc]
  obtain ⟨g, hg⟩ := key q
  obtain ⟨g', hg'⟩ := key q⁻¹
  have hcomp : ∀ (r : EtaleFundamentalGroup X x ⧸ V) (a b : Y ⟶ Y),
      (∀ y, (finiteEtaleFiberFunctor x).map a y = e.symm (e y * r)) →
      (∀ y, (finiteEtaleFiberFunctor x).map b y = e.symm (e y * r⁻¹)) → a ≫ b = 𝟙 Y := by
    intro r a b ha hb
    refine finiteEtaleFiberFunctor_map_injective x fun y ↦ ?_
    rw [Functor.map_comp_apply, ha, hb, Equiv.apply_symm_apply, mul_assoc,
      mul_inv_cancel, mul_one, Equiv.symm_apply_apply, Functor.map_id_apply]
  refine ⟨⟨g, g', hcomp q g g' hg hg', ?_⟩, hg⟩
  simpa using hcomp q⁻¹ g' g hg' (by simpa using hg)

/-! ### The degree of a Galois object is the order of its automorphism group -/

/-- **The Galois group of a Galois object has order its degree.** The automorphism group of a
Galois object of `FÉt_X` acts simply transitively on a geometric fibre
(`CategoryTheory.PreGaloisCategory.evaluation_aut_bijective_of_isGalois`), so its order is the
cardinality of that fibre.

This is the dictionary between the two ways the prime-to-`p` condition of [Stacks, Tag 0C0R] is
stated: "the Galois group has order prime to `p`" and "the cover has degree prime to `p`". The
Galois group in question is the group of
`AlgebraicGeometry.FiniteEtaleGaloisCover.ofIsGalois`, namely `Aut A`. -/
theorem card_aut_eq_card_fiber_of_isGalois (A : FiniteEtaleOver X) [IsGalois A] :
    Nat.card (Aut A) = Nat.card ((finiteEtaleFiberFunctor x).obj A) := by
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected (finiteEtaleFiberFintypeFunctor X x) A
  exact Nat.card_eq_of_bijective (fun φ : Aut A ↦ (finiteEtaleFiberFunctor x).map φ.hom a)
    (evaluation_aut_bijective_of_isGalois (finiteEtaleFiberFintypeFunctor X x) A a)

/-! ### An open normal subgroup is the stabilizer on a Galois cover of the expected degree -/

/-- **An open normal subgroup of `π₁(X, x)` is realized by a Galois cover of the corresponding
degree.** Let `X` be a connected scheme with a geometric point `x` and let `V` be an open normal
subgroup of `π₁(X, x)`. Then there is a finite étale cover `Y` of `X` which is a Galois object of
`FÉt_X`, a point `y` of its geometric fibre whose stabilizer is `V`, and the geometric fibre of
`Y` has exactly `[π₁(X, x) : V]` elements.

The cover is the one attached to the finite continuous `π₁(X, x)`-set `π₁(X, x)/V`; the stabilizer
of the coset of `1` is `V`, the cardinality of the fibre is the index by construction, the total
space is connected because the action on a coset space is transitive
(`AlgebraicGeometry.connectedSpace_left_of_isPretransitive`), and `Aut Y` acts transitively on the
fibre by `AlgebraicGeometry.EtaleFundamentalGroup.exists_aut_map_eq_mul_of_fiberEquiv`. -/
@[sga "1 V 5.11" "standard case"]
theorem exists_isGalois_card_fiber_eq_index_stabilizer_eq_of_isOpen
    (V : Subgroup (EtaleFundamentalGroup X x)) (hVnorm : V.Normal)
    (hV : IsOpen (V : Set (EtaleFundamentalGroup X x))) :
    ∃ (Y : FiniteEtaleOver X) (y : (finiteEtaleFiberFunctor x).obj Y),
      IsGalois Y ∧ Nat.card ((finiteEtaleFiberFunctor x).obj Y) = V.index ∧
        MulAction.stabilizer (EtaleFundamentalGroup X x) y = V := by
  have := hVnorm
  have : ∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y) := finite_finiteEtaleFiber x
  have : Finite (EtaleFundamentalGroup X x ⧸ V) := Subgroup.quotient_finite_of_isOpen V hV
  obtain ⟨Y, e, he⟩ := exists_finiteEtaleOver_fiber_equiv x (EtaleFundamentalGroup X x ⧸ V)
    (isOpen_stabilizer_quotient x V hV)
  set y₀ : (finiteEtaleFiberFunctor x).obj Y :=
    e.symm (QuotientGroup.mk 1 : EtaleFundamentalGroup X x ⧸ V) with hy₀
  -- the coset of `1` has stabilizer `V`
  have hstab : MulAction.stabilizer (EtaleFundamentalGroup X x) y₀ = V := by
    ext σ
    rw [MulAction.mem_stabilizer_iff, ← e.injective.eq_iff, he, hy₀, Equiv.apply_symm_apply,
      smul_quotient_eq_mul, QuotientGroup.mk_one, mul_one, QuotientGroup.eq_one_iff]
  -- the fundamental group acts transitively on the fibre
  have htrans : ∀ y : (finiteEtaleFiberFunctor x).obj Y,
      ∃ σ : EtaleFundamentalGroup X x, σ • y₀ = y := by
    intro y
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (s := V) (e y)
    refine ⟨a, e.injective ?_⟩
    rw [he, hy₀, Equiv.apply_symm_apply, ← ha, smul_quotient_eq_mul, QuotientGroup.mk_one,
      mul_one]
  have : ConnectedSpace Y.left := connectedSpace_left_of_isPretransitive x Y y₀ htrans
  have : PreGaloisCategory.IsConnected Y := isConnected_of_connectedSpace_left Y
  refine ⟨Y, y₀, ?_, (Nat.card_congr e).trans (Subgroup.index_eq_card V).symm, hstab⟩
  rw [isGalois_iff_pretransitive (finiteEtaleFiberFintypeFunctor X x) Y]
  refine isPretransitive_aut_of_forall_exists_map_eq x Y fun a b ↦ ?_
  obtain ⟨φ, hφ⟩ := exists_aut_map_eq_mul_of_fiberEquiv x V Y e he ((e a)⁻¹ * e b)
  exact ⟨φ, by rw [hφ, mul_inv_cancel_left, Equiv.symm_apply_apply]⟩

end EtaleFundamentalGroup

end AlgebraicGeometry

end
