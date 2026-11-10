module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksCore.Tactic.StacksAttribute

/-!
# The constant presheaf, the constant sheaf, and their stalks

Fix a topological space `X`, a set `A` and a point `x ∈ X`. Stacks 007B introduces the constant
presheaf `A_p` with value `A`, the canonical map of presheaves `c : A_p → A̲` into the constant
sheaf `A̲` with value `A`, and asserts the canonical bijections `A = (A_p)_x = A̲_x`, the second
one induced by functoriality of stalks from `c`.

Following Stacks 0081, `A̲` is taken to be the sheafification of `A_p` and `c` to be the
sheafification unit: `constPresheaf` is the constant functor with value `A` and identity
restriction maps, `constSheaf` is `(constPresheaf X A).sheafify` (Mathlib's explicit germ-tuple
sheafification) and `constSheafUnit` is its unit `toSheafify`.

The first bijection is `alphaX_bijective`, for the map `alphaX : A → (A_p)_x` sending `a` to the
germ at `x` of the constant section `a`, represented on the neighbourhood `U = ⊤`;
`alphaX_germ_eq` records that this germ does not depend on which open neighbourhood of `x` is
used. The second is `cX_bijective`, for the map `cX : (A_p)_x → A̲_x` obtained by applying
`TopCat.Presheaf.stalkFunctor` to `constSheafUnit`; its proof goes through `stalkToFiber_cX`,
which exhibits `cX` as a section of Mathlib's bijection `stalkToFiber`. The composite
`betaX = cX ∘ alphaX : A → A̲_x` is then bijective by `betaX_bijective`.

## References

* [Stacks Project, Tag 007B](https://stacks.math.columbia.edu/tag/007B)
* [Stacks Project, Tag 006F](https://stacks.math.columbia.edu/tag/006F)
* [Stacks Project, Tag 0081](https://stacks.math.columbia.edu/tag/0081)
-/

@[expose] public section

open TopCat CategoryTheory Opposite TopologicalSpace

universe u

variable (X : TopCat.{u}) (A : Type u) (x : X)

/-- The constant presheaf with value `A`: the presheaf `A_p` with
`A_p(U) = A` for every open `U ⊆ X` and every restriction map equal to `id_A`. This is the
constant functor `(Opens X)ᵒᵖ ⥤ Type` with value `A`. -/
@[ega "0 3.6.1",
  sga "4 IV 2.7.5" "special case",
  sga "4 IV 4.3.4" "special case",
  sga "4 IX 2.0" "partial"]
noncomputable def constPresheaf : TopCat.Presheaf (Type u) X := (Functor.const _).obj A

/-- The constant sheaf with value `A`, `A̲ := (A_p)^#`, defined as the sheafification of the
constant presheaf, following Stacks 0081. -/
@[ega "0 3.6.1",
  sga "4 IV 11.1.5" "partial",
  sga "4 IV 2.7.5" "special case",
  sga "4 IV 4.3.4" "special case",
  sga "4 IX 2.0" "constant sheaf S_T"]
noncomputable def constSheaf : TopCat.Sheaf (Type u) X := (constPresheaf X A).sheafify

/-- The canonical map of presheaves `c : A_p → A̲`, namely the sheafification unit
`θ : A_p → (A_p)^#`. -/
noncomputable def constSheafUnit :
    constPresheaf X A ⟶ (constSheaf X A).presheaf :=
  (constPresheaf X A).toSheafify

/-- The map `α_x : A → (A_p)_x`, `a ↦ (U, a)_x`, realized as the germ at `x` of the
constant section `a` over `U = ⊤ = X` (which always contains `x`). -/
noncomputable def alphaX : A → (constPresheaf X A).stalk x :=
  fun a => (constPresheaf X A).germ ⊤ x trivial a

/-- The map on stalks `c_x : (A_p)_x → A̲_x` induced by `c = constSheafUnit`, obtained by
applying the stalk functor of Stacks 0078 to it. -/
noncomputable def cX :
    (constPresheaf X A).stalk x ⟶ (constSheaf X A).presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor (Type u) x).map (constSheafUnit X A)

/-- The composite `β_x := c_x ∘ α_x : A → A̲_x`. -/
noncomputable def betaX : A → (constSheaf X A).presheaf.stalk x :=
  fun a => cX X A x (alphaX X A x a)

/-- Well-definedness of `α_x`: for any open `U ∋ x`, the germ at `x` of the constant section
`a ∈ A_p(U)` equals `α_x a`, so `α_x` does not depend on the chosen open neighbourhood of
`x`. -/
theorem alphaX_germ_eq (a : A) (U : Opens X) (hx : x ∈ U) :
    (constPresheaf X A).germ U x hx a = alphaX X A x a := by
  unfold alphaX
  have i : U ⟶ ⊤ := homOfLE le_top
  rw [← (constPresheaf X A).germ_res i x hx]
  rfl

/-- The canonical bijection `A = (A_p)_x`: the map `α_x : A → (A_p)_x` is bijective. -/
@[stacks 007B]
theorem alphaX_bijective : Function.Bijective (alphaX X A x) := by
  refine ⟨fun a b hab => ?_, fun t => ?_⟩
  · have hxtop : x ∈ (⊤ : Opens X) := trivial
    have heq : (ConcreteCategory.hom ((constPresheaf X A).germ ⊤ x hxtop)) a
        = (ConcreteCategory.hom ((constPresheaf X A).germ ⊤ x hxtop)) b := hab
    obtain ⟨W, hW, iU, iV, hmap⟩ :=
      (constPresheaf X A).germ_eq x hxtop hxtop a b heq
    -- both maps are identity on the constant presheaf
    simp only [constPresheaf, Functor.const_obj_map] at hmap
    exact hmap
  · obtain ⟨U, m, s, hs⟩ := (constPresheaf X A).exists_germ_eq t
    exact ⟨s, (alphaX_germ_eq X A x s U m).symm.trans hs⟩

-- `(constSheaf X A).presheaf` and `subsheafToTypes (isLocallyGerm …)` are only definitionally
-- equal, not syntactically equal, so the strict isDefEq-transparency check must be relaxed.
set_option backward.isDefEq.respectTransparency.types false in
/-- The composite `stalkToFiber x ∘ cX = id` on the stalk of the constant presheaf. -/
theorem stalkToFiber_cX (y : (constPresheaf X A).stalk x) :
    (constPresheaf X A).stalkToFiber x (cX X A x y) = y := by
  obtain ⟨U, m, s, rfl⟩ := (constPresheaf X A).exists_germ_eq y
  -- cX (germ U x m s) = sheafify.germ U x m (toSheafify.app s)
  have hcx : (ConcreteCategory.hom (cX X A x))
      ((ConcreteCategory.hom ((constPresheaf X A).germ U x m)) s) =
      (ConcreteCategory.hom ((constSheaf X A).presheaf.germ U x m))
        ((ConcreteCategory.hom ((constSheafUnit X A).app (op U))) s) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply U x m (constSheafUnit X A) s
  change (ConcreteCategory.hom ((constPresheaf X A).stalkToFiber x))
      ((ConcreteCategory.hom (cX X A x)) ((ConcreteCategory.hom ((constPresheaf X A).germ U x m))
          s)) = _
  rw [hcx]
  change TopCat.stalkToFiber (TopCat.Presheaf.Sheafify.isLocallyGerm (constPresheaf X A)) x
      ((TopCat.subsheafToTypes (TopCat.Presheaf.Sheafify.isLocallyGerm (constPresheaf X
          A))).presheaf.germ U x m
          ((constSheafUnit X A).app (op U) s)) = _
  rw [TopCat.stalkToFiber_germ]
  rfl

/-- The map on stalks `c_x : (A_p)_x → A̲_x` induced by functoriality from `c : A_p → A̲` is a
bijection. -/
@[stacks 007B]
theorem cX_bijective : Function.Bijective (cX X A x) := by
  -- cX is a right inverse of the bijective stalkToFiber, hence bijective
  refine ⟨Function.LeftInverse.injective (stalkToFiber_cX X A x), fun z => ?_⟩
  refine ⟨(constPresheaf X A).stalkToFiber x z, ?_⟩
  apply (constPresheaf X A).stalkToFiber_injective x
  rw [stalkToFiber_cX]

/-- The canonical bijection `A = A̲_x`: the composite `β_x := c_x ∘ α_x : A → A̲_x` is
bijective. -/
@[stacks 007B]
theorem betaX_bijective : Function.Bijective (betaX X A x) :=
  (cX_bijective X A x).comp (alphaX_bijective X A x)
