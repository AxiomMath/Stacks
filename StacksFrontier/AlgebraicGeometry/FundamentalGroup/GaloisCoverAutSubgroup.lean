module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.GaloisSubgroupQuotient
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverTorsor

/-!
# A Galois cover with group `G` is a Galois object with `Aut` identified with `G`

Let `X` be a connected scheme and `Z` a finite étale Galois cover of `X` with group `G`, in the
torsor sense of `AlgebraicGeometry.FiniteEtaleGaloisCover`: the total space is connected and the
comparison `G × Z ⟶ Z ×_X Z` is an isomorphism. This file identifies that presentation with the
one the quotient construction `AlgebraicGeometry.galoisSubgroupQuotient` uses, namely a Galois
object `A` of the Galois category `FÉt_X` together with a subgroup of `Aut A`.

The lifts of a geometric point of `X` to `Z` form a `G`-torsor, because the source of a geometric
point is a one-point scheme and
`AlgebraicGeometry.Abhyankar.existsUnique_comp_twist` says the lifts through a torsor form one.
Hence `G` acts simply transitively on every geometric fibre of `Z`, so

* `Z.obj` is a connected object of `FÉt_X` on whose fibres `Aut Z.obj` acts transitively, i.e. a
  Galois object, and
* `σ ↦ σ⁻¹` followed by the action is an isomorphism `G ≃* Aut Z.obj`, since it is injective by
  simple transitivity and surjective because an automorphism of a connected cover is determined
  by its value at one fibre point.

Transporting a subgroup `H ≤ G` along that isomorphism therefore feeds
`AlgebraicGeometry.galoisSubgroupQuotient` with the index preserved, so the quotient `Z/H` is
finite étale of degree `[G : H]` and `Z ⟶ Z/H` is a Galois covering with group `H` whenever `X`
is irreducible and geometrically unibranch.

## Main definitions

* `AlgebraicGeometry.FiniteEtaleGaloisCover.autHom`: the group map `G →* Aut Z.obj`.
* `AlgebraicGeometry.FiniteEtaleGaloisCover.autMulEquiv`: it is an isomorphism.
* `AlgebraicGeometry.FiniteEtaleGaloisCover.autSubgroup`: the subgroup of `Aut Z.obj` attached to
  a subgroup of `G`.
* `AlgebraicGeometry.FiniteEtaleGaloisCover.quotient` and
  `AlgebraicGeometry.FiniteEtaleGaloisCover.quotientπ`: the quotient `Z/H` and its projection.
* `AlgebraicGeometry.FiniteEtaleGaloisCover.quotientCovering`: `Z ⟶ Z/H` as a Galois covering.

## Main results

* `AlgebraicGeometry.FiniteEtaleGaloisCover.existsUnique_action_smul_eq`: `G` acts simply
  transitively on every geometric fibre.
* `AlgebraicGeometry.FiniteEtaleGaloisCover.isGalois_obj`: `Z.obj` is a Galois object of `FÉt_X`.
* `AlgebraicGeometry.FiniteEtaleGaloisCover.index_autSubgroup`: the transported subgroup has the
  same index.
* `AlgebraicGeometry.FiniteEtaleGaloisCover.isFiniteLocallyFreeOfRank_quotient`: `Z/H` has degree
  `[G : H]` over `X`.

## References

* [Stacks Project, Section 03SF](https://stacks.math.columbia.edu/tag/03SF)
* [Stacks Project, Tag 0BN2](https://stacks.math.columbia.edu/tag/0BN2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

universe v u

namespace AlgebraicGeometry

/-- A nonempty scheme carries a geometric point: the algebraically closed point above any one of
its points. -/
private theorem nonempty_geometricPoint (X : Scheme.{u}) [Nonempty X] :
    Nonempty (GeometricPoint X) :=
  ⟨X.algClosedPoint (Classical.arbitrary X)⟩

namespace FiniteEtaleGaloisCover

variable {X : Scheme.{u}} [ConnectedSpace X] {G : Type v} [Group G] [Finite G]
  (Z : FiniteEtaleGaloisCover X G)

/-- The total space of a finite étale Galois cover is a connected object of `FÉt_X`: it is
connected as a topological space, and the two notions agree. -/
instance isConnected_obj : IsConnected Z.obj :=
  isConnected_of_connectedSpace_left Z.obj

/-- **The lifts of a geometric point to a Galois cover form a `G`-torsor.** The source of a
geometric point is a one-point scheme, so this is the torsor property of the lifts through the
comparison isomorphism. -/
theorem existsUnique_comp_action_eq (x : GeometricPoint X)
    (a b : (finiteEtaleFiberFintypeFunctor X x).obj Z.obj) :
    ∃! σ : G, a.1 ≫ (Z.action (.op σ)).asIso.hom.left = b.1 :=
  Abhyankar.existsUnique_comp_twist Z.obj.hom
    (((MorphismProperty.Over.forget finiteEtale ⊤ X).mapAut Z.obj).comp Z.action) a.1 b.1
    (b.2.trans a.2.symm)

/-- **`G` acts simply transitively on every geometric fibre of a Galois cover.** -/
theorem existsUnique_action_smul_eq (x : GeometricPoint X)
    (a b : (finiteEtaleFiberFintypeFunctor X x).obj Z.obj) :
    ∃! σ : G, Z.action (.op σ) • a = b := by
  obtain ⟨σ, hσ, huniq⟩ := Z.existsUnique_comp_action_eq x a b
  exact ⟨σ, Subtype.ext hσ, fun τ hτ ↦ huniq τ (congrArg Subtype.val hτ)⟩

/-- **The total space of a finite étale Galois cover is a Galois object of `FÉt_X`.** It is
connected, and its automorphism group already contains the simply transitive action of `G` on a
geometric fibre. -/
instance isGalois_obj : IsGalois Z.obj := by
  obtain ⟨x⟩ := nonempty_geometricPoint X
  rw [isGalois_iff_pretransitive (finiteEtaleFiberFintypeFunctor X x) Z.obj]
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨σ, hσ, -⟩ := Z.existsUnique_action_smul_eq x a b
  exact ⟨Z.action (.op σ), hσ⟩

/-- The automorphism of the total space attached to an element of the group of a Galois cover.
The action is a right action, so the inverse makes it a homomorphism. -/
def autHom : G →* Aut Z.obj :=
  Z.action.comp (MulEquiv.inv' G).toMonoidHom

omit [ConnectedSpace X] in
/-- The automorphism attached to `σ` is the action of `σ⁻¹`. -/
theorem autHom_apply (σ : G) : Z.autHom σ = Z.action (.op σ⁻¹) :=
  rfl

/-- An element of the group of a Galois cover acting as the identity is the identity: it and `1`
both fix a point of a geometric fibre, on which the action is simply transitive. -/
theorem eq_one_of_action_eq_one (x : GeometricPoint X) {σ : G} (h : Z.action (.op σ) = 1) :
    σ = 1 := by
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected (finiteEtaleFiberFintypeFunctor X x) Z.obj
  refine (Z.existsUnique_action_smul_eq x a a).unique ?_ ?_
  · rw [h, one_smul]
  · rw [MulOpposite.op_one, map_one, one_smul]

/-- The map from the group of a Galois cover to the automorphism group of its total space is
injective. -/
theorem autHom_injective : Function.Injective Z.autHom := by
  obtain ⟨x⟩ := nonempty_geometricPoint X
  rw [injective_iff_map_eq_one]
  intro σ hσ
  exact inv_eq_one.mp (Z.eq_one_of_action_eq_one x hσ)

/-- The map from the group of a Galois cover to the automorphism group of its total space is
surjective. -/
theorem autHom_surjective : Function.Surjective Z.autHom := by
  obtain ⟨x⟩ := nonempty_geometricPoint X
  intro τ
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected (finiteEtaleFiberFintypeFunctor X x) Z.obj
  obtain ⟨σ, hσ, -⟩ := Z.existsUnique_action_smul_eq x a (τ • a)
  refine ⟨σ⁻¹, ?_⟩
  rw [Z.autHom_apply, inv_inv]
  exact evaluation_aut_injective_of_isConnected (finiteEtaleFiberFintypeFunctor X x) Z.obj a hσ

/-- **The group of a finite étale Galois cover is the automorphism group of its total space.**
Injectivity is the freeness of the action on a geometric fibre; surjectivity holds because an
automorphism of a connected cover is determined by its value at one fibre point, and the action
of `G` already reaches every value. -/
def autMulEquiv : G ≃* Aut Z.obj :=
  MulEquiv.ofBijective Z.autHom ⟨Z.autHom_injective, Z.autHom_surjective⟩

/-- The isomorphism `G ≃* Aut Z.obj` sends `σ` to the action of `σ⁻¹`. -/
@[simp]
theorem autMulEquiv_apply (σ : G) : Z.autMulEquiv σ = Z.action (.op σ⁻¹) :=
  rfl

variable (H : Subgroup G)

/-- The subgroup of `Aut Z.obj` attached to a subgroup of the group of a Galois cover: its image
under `AlgebraicGeometry.FiniteEtaleGaloisCover.autHom`. This is the key of the quotient
construction `AlgebraicGeometry.galoisSubgroupQuotient`. -/
def autSubgroup : Subgroup (Aut Z.obj) :=
  H.map Z.autHom

/-- A subgroup of the group of a Galois cover is isomorphic to its image in `Aut Z.obj`. -/
def autSubgroupMulEquiv : H ≃* Z.autSubgroup H :=
  H.equivMapOfInjective Z.autHom Z.autHom_injective

/-- **Transporting a subgroup to `Aut Z.obj` preserves the index.** -/
theorem index_autSubgroup : (Z.autSubgroup H).index = H.index :=
  Subgroup.index_map_of_bijective ⟨Z.autHom_injective, Z.autHom_surjective⟩ H

omit [ConnectedSpace X] in
/-- For `σ ∈ H`, the action of `σ⁻¹` lies in the subgroup of `Aut Z.obj` attached to `H`. -/
theorem mem_autSubgroup_action (σ : G) (hσ : σ ∈ H) : Z.action (.op σ⁻¹) ∈ Z.autSubgroup H :=
  Subgroup.mem_map_of_mem _ hσ

/-! ### The quotient of a Galois cover by a subgroup of its group -/

/-- **The quotient `Z/H`** of a finite étale Galois cover by a subgroup of its group, as a finite
étale cover of `X`. -/
def quotient : FiniteEtaleOver X :=
  galoisSubgroupQuotient Z.obj (Z.autSubgroup H)

/-- The projection `Z ⟶ Z/H`. -/
def quotientπ : Z.obj ⟶ Z.quotient H :=
  galoisSubgroupQuotientπ Z.obj (Z.autSubgroup H)

/-- **The degree of `Z/H` over `X` is the index of `H` in `G`.** -/
theorem isFiniteLocallyFreeOfRank_quotient (x : GeometricPoint X) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (Z.quotient H).hom H.index :=
  Z.index_autSubgroup H ▸
    isFiniteLocallyFreeOfRank_galoisSubgroupQuotient Z.obj (Z.autSubgroup H) x

/-- **Every point of a geometric fibre of `Z/H` comes from `Z`.** -/
theorem exists_map_quotientπ_eq (x : GeometricPoint X)
    (t : (finiteEtaleFiberFintypeFunctor X x).obj (Z.quotient H)) :
    ∃ a, (finiteEtaleFiberFintypeFunctor X x).map (Z.quotientπ H) a = t :=
  exists_map_galoisSubgroupQuotientπ_eq Z.obj (Z.autSubgroup H) x t

/-- **Two points of a geometric fibre of `Z` with the same image in `Z/H` differ by an element of
`H`.** -/
theorem exists_mem_smul_eq_of_map_quotientπ_eq (x : GeometricPoint X)
    {a b : (finiteEtaleFiberFintypeFunctor X x).obj Z.obj}
    (hab : (finiteEtaleFiberFintypeFunctor X x).map (Z.quotientπ H) a =
      (finiteEtaleFiberFintypeFunctor X x).map (Z.quotientπ H) b) :
    ∃ σ ∈ H, Z.action (.op σ) • a = b := by
  obtain ⟨⟨-, σ, hσ, rfl⟩, hab'⟩ :=
    exists_smul_eq_of_map_galoisSubgroupQuotientπ_eq Z.obj (Z.autSubgroup H) x hab
  exact ⟨σ⁻¹, H.inv_mem hσ, hab'⟩

variable [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)

include hX in
/-- **`Z ⟶ Z/H` is a Galois covering with group the image of `H` in `Aut Z.obj`**, which
`AlgebraicGeometry.FiniteEtaleGaloisCover.autSubgroupMulEquiv` identifies with `H`. -/
def quotientCovering : EtaleGaloisCovering (Z.quotient H).left (Z.autSubgroup H) :=
  galoisSubgroupQuotientCovering Z.obj (Z.autSubgroup H) hX

end FiniteEtaleGaloisCover

end AlgebraicGeometry

end
