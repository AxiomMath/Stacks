module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack

/-! # Gerbes over a site

A *gerbe* over a site `(𝒞, J)` is a stack in groupoids `p : 𝒮 ⥤ 𝒞` which is moreover
*locally nonempty* — every object of `𝒞` has a covering along whose members `𝒮` has an
object — and *locally connected* — any two objects of a fibre become isomorphic after
restriction along the members of some covering. These are conditions (1), (2) and (3) of
Stacks 06NZ.

## Main definitions

* `CategoryTheory.Functor.LocallyNonempty`: local nonemptiness, condition (2).
* `CategoryTheory.Functor.LocallyConnected`: local connectedness, condition (3).
* `CategoryTheory.Functor.IsGerbe`: gerbes over a site.
* `CategoryTheory.Functor.LocallyNonemptyFamily` and
  `CategoryTheory.Functor.LocallyConnectedFamily`: conditions (2) and (3) quantified over a
  covering *family* `{U_i → U}` rather than over a covering sieve.

## Main results

* `CategoryTheory.Functor.locallyNonempty_iff_family` and
  `CategoryTheory.Functor.locallyConnected_iff_family`: for a category fibred in groupoids, the
  sieve and the family forms of conditions (2) and (3) are equivalent.
-/

@[expose] public section

open CategoryTheory

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} {𝒮 : Type u₂} [Category.{v₁} 𝒞] [Category.{v₂} 𝒮]

/-- `p : 𝒮 ⥤ 𝒞` is *locally nonempty* for the topology `J`: every object `U` of `𝒞` admits a
covering sieve along every arrow `f : V ⟶ U` of which the fibre category `𝒮_V` is nonempty. -/
def LocallyNonempty (p : 𝒮 ⥤ 𝒞) (J : GrothendieckTopology 𝒞) : Prop :=
  ∀ U : 𝒞, ∃ S ∈ J U, ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), S f → Nonempty (p.Fiber V)

/-- `p : 𝒮 ⥤ 𝒞` is *locally connected* for the topology `J`: for any two objects `x`, `y` of a
fibre category `𝒮_U` there is a covering sieve of `U` along every arrow `f : V ⟶ U` of which the
restrictions of `x` and of `y` are isomorphic in `𝒮_V`. The restrictions are given as objects `x₁`,
`y₁` with morphisms to `x`, `y` lying over `f`, and the isomorphism between them is required to lie
over `𝟙 V`, that is to be an isomorphism of the fibre category over `V`. -/
def LocallyConnected (p : 𝒮 ⥤ 𝒞) (J : GrothendieckTopology 𝒞) : Prop :=
  ∀ ⦃U : 𝒞⦄ (x y : 𝒮), p.obj x = U → p.obj y = U → ∃ S ∈ J U,
    ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), S f →
      ∃ (x₁ y₁ : 𝒮) (ξ : x₁ ⟶ x) (υ : y₁ ⟶ y) (e : x₁ ≅ y₁),
        p.IsHomLift f ξ ∧ p.IsHomLift f υ ∧ p.IsHomLift (𝟙 V) e.hom

/-- A *gerbe* over the site `(𝒞, J)` is a category `p : 𝒮 ⥤ 𝒞` over `𝒞` which is a stack in
groupoids over `𝒞` (Stacks 02ZI), locally nonempty, and locally connected. -/
@[stacks 06NZ]
def IsGerbe (p : 𝒮 ⥤ 𝒞) (J : GrothendieckTopology 𝒞) : Prop :=
  IsStackInGroupoids.{w} p J ∧ LocallyNonempty p J ∧ LocallyConnected p J

/-! ### The local conditions, stated with covering families -/

/-- Local nonemptiness stated with covering families: for every `U` there is a covering *family*
`{f i : V i ⟶ U}`, one whose generated sieve is covering, such that each `𝒮_{V i}` is nonempty. -/
def LocallyNonemptyFamily (p : 𝒮 ⥤ 𝒞) (J : GrothendieckTopology 𝒞) : Prop :=
  ∀ U : 𝒞, ∃ (I : Type w) (V : I → 𝒞) (f : ∀ i, V i ⟶ U),
    Sieve.ofArrows V f ∈ J U ∧ ∀ i, Nonempty (p.Fiber (V i))

/-- Local connectedness stated with covering families: for `x`, `y` in `𝒮_U` there is a covering
*family* `{f i : V i ⟶ U}` such that the restrictions of `x` and `y` along each `f i` are
isomorphic in `𝒮_{V i}`. -/
def LocallyConnectedFamily (p : 𝒮 ⥤ 𝒞) (J : GrothendieckTopology 𝒞) : Prop :=
  ∀ ⦃U : 𝒞⦄ (x y : 𝒮), p.obj x = U → p.obj y = U →
    ∃ (I : Type w) (V : I → 𝒞) (f : ∀ i, V i ⟶ U), Sieve.ofArrows V f ∈ J U ∧
      ∀ i, ∃ (x₁ y₁ : 𝒮) (ξ : x₁ ⟶ x) (υ : y₁ ⟶ y) (e : x₁ ≅ y₁),
        p.IsHomLift (f i) ξ ∧ p.IsHomLift (f i) υ ∧ p.IsHomLift (𝟙 (V i)) e.hom

end CategoryTheory.Functor

namespace CategoryTheory.Sieve

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- The family of *all* arrows of a sieve `S` on `U` generates `S`. -/
theorem ofArrows_sigma_arrows {U : 𝒞} (S : Sieve U) :
    Sieve.ofArrows (fun (i : Σ V : 𝒞, {f : V ⟶ U // S.arrows f}) => i.1)
      (fun i => i.2.val) = S := by
  ext V f
  rw [Sieve.mem_ofArrows_iff]
  refine ⟨?_, fun hf ↦ ⟨⟨V, f, hf⟩, 𝟙 V, (Category.id_comp f).symm⟩⟩
  rintro ⟨i, a, rfl⟩
  exact S.downward_closed i.2.property a

end CategoryTheory.Sieve

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} {𝒮 : Type u₂} [Category.{v₁} 𝒞] [Category.{v₂} 𝒮]

/-- A covering sieve `S` yields a covering family, indexed by all arrows of `S`, whose members
all satisfy any property `P` that holds on the arrows of `S`. -/
private theorem exists_covering_family_of_mem {U : 𝒞} {J : GrothendieckTopology 𝒞}
    {S : Sieve U} (hS : S ∈ J U) {P : ∀ ⦃V : 𝒞⦄, (V ⟶ U) → Prop}
    (h : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), S f → P f) :
    ∃ (I : Type max u₁ v₁) (V : I → 𝒞) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧ ∀ i, P (f i) :=
  ⟨Σ V : 𝒞, {f : V ⟶ U // S.arrows f}, fun i => i.1, fun i => i.2.val,
    (Sieve.ofArrows_sigma_arrows S).symm ▸ hS, fun ⟨_, f, hf⟩ ↦ h f hf⟩

/-- For a category fibred in groupoids, local nonemptiness is equivalent to its covering-family
form `CategoryTheory.Functor.LocallyNonemptyFamily`. -/
theorem locallyNonempty_iff_family {p : 𝒮 ⥤ 𝒞} (hp : p.IsFiberedInGroupoids)
    (J : GrothendieckTopology 𝒞) :
    LocallyNonempty p J ↔ LocallyNonemptyFamily.{max u₁ v₁} p J := by
  refine ⟨fun h U ↦ ?_, fun h U ↦ ?_⟩
  · obtain ⟨S, hS, hne⟩ := h U
    exact exists_covering_family_of_mem hS hne
  · obtain ⟨I, V, f, hcov, hne⟩ := h U
    refine ⟨Sieve.ofArrows V f, hcov, fun W g hg ↦ ?_⟩
    obtain ⟨i, a, rfl⟩ := Sieve.mem_ofArrows_iff .. |>.1 hg
    obtain ⟨x⟩ := hne i
    obtain ⟨y, φ, hφ⟩ := hp.exists_lift a x.1 x.2
    exact ⟨⟨y, IsHomLift.domain_eq p a φ⟩⟩

/-- For a category fibred in groupoids, local connectedness is equivalent to its covering-family
form `CategoryTheory.Functor.LocallyConnectedFamily`. -/
theorem locallyConnected_iff_family {p : 𝒮 ⥤ 𝒞} (hp : p.IsFiberedInGroupoids)
    (J : GrothendieckTopology 𝒞) :
    LocallyConnected p J ↔ LocallyConnectedFamily.{max u₁ v₁} p J := by
  refine ⟨fun h U x y hx hy ↦ ?_, fun h U x y hx hy ↦ ?_⟩
  · obtain ⟨S, hS, hiso⟩ := h x y hx hy
    exact exists_covering_family_of_mem hS hiso
  · obtain ⟨I, V, f, hcov, hiso⟩ := h x y hx hy
    refine ⟨Sieve.ofArrows V f, hcov, fun W g hg ↦ ?_⟩
    obtain ⟨i, a, rfl⟩ := Sieve.mem_ofArrows_iff .. |>.1 hg
    obtain ⟨x₁, y₁, ξ, υ, e, hξ, hυ, he⟩ := hiso i
    obtain ⟨x₂, α, hα⟩ := hp.exists_lift a x₁ (IsHomLift.domain_eq p (f i) ξ)
    obtain ⟨y₂, β, hβ⟩ := hp.exists_lift a y₁ (IsHomLift.domain_eq p (f i) υ)
    have hβsc : p.IsStronglyCartesian a β := hp.isStronglyCartesian_homLift a β
    have hαe : p.IsHomLift (𝟙 W ≫ a) (α ≫ e.hom) := by
      simpa using (inferInstance : p.IsHomLift (a ≫ 𝟙 (V i)) (α ≫ e.hom))
    set χ := IsStronglyCartesian.map p a β (g := 𝟙 W) rfl (α ≫ e.hom) with hχ
    have hχlift : p.IsHomLift (𝟙 W) χ := IsStronglyCartesian.map_isHomLift p a β rfl (α ≫ e.hom)
    have hχsc : p.IsStronglyCartesian (𝟙 W) χ := hp.isStronglyCartesian_homLift (𝟙 W) χ
    have : IsIso χ := IsStronglyCartesian.isIso_of_base_isIso (p := p) (f := 𝟙 W) χ
    exact ⟨x₂, y₂, α ≫ ξ, β ≫ υ, asIso χ, inferInstance, inferInstance, hχlift⟩

end CategoryTheory.Functor
