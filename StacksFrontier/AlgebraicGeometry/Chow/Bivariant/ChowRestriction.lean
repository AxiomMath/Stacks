module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Commuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Definition
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible

/-!
# Restriction of bivariant classes (Stacks 0F9Z)

Let `(S, δ)` be as in Situation 02QL, let `f : X ⟶ Y` and `h : Y' ⟶ Y` be morphisms of schemes
locally of finite type over `S` and let `X' = Y' ×_Y X`. A scheme `Y''` locally of finite type over
`Y'` is one over `Y`, so a bivariant class `c ∈ A^p(X ⟶ Y)` caps on the Chow groups of `Y''`; this
gives the restriction

  `A^p(X ⟶ Y) ⟶ A^p(X' ⟶ Y')`,  `c ↦ res(c)`,  `res(c) ∩ α'' = c ∩ α''`,

which is compatible with compositions. The bivariant classes are those of
`Stacks.Chow.BivariantChowClass`, of Stacks 0B76.

## Main definitions

* `Stacks.Chow.BivariantChowClass.restrict` — the restriction `res(c)` of a bivariant class along
  `h : Y' ⟶ Y`.
* `Stacks.Chow.BivariantChowClass.restrictAddHom` — the restriction map
  `A^p(X ⟶ Y) ⟶ A^p(X' ⟶ Y')` as a homomorphism of groups.
* `Stacks.Chow.BivariantChowClass.comp` — the composition
  `A^p(X ⟶ Y) × A^q(Y ⟶ Z) ⟶ A^{p+q}(X ⟶ Z)` of Stacks 0B75, `(a ∘ b) ∩ α = a ∩ (b ∩ α)`.
* `Stacks.Chow.BivariantChowClass.transport` — transport of a bivariant class along an isomorphism
  `A ≅ B` over `W`, `A^p(A ⟶ W) = A^p(B ⟶ W)`.

## Main results

* `Stacks.Chow.BivariantChowClass.restrict_cap` — `res(c) ∩ α'' = c ∩ α''`, read on
  `(Y' ×_Y X) ×_{Y'} Y''` through the canonical isomorphism with `Y'' ×_Y X`.
* `Stacks.Chow.BivariantChowClass.restrict_restrict` — compatibility with composition of base
  changes: restricting along `h` and then along `h' : Y'' ⟶ Y'` is restricting along `h' ≫ h`,
  up to the canonical isomorphism of the sources.
* `Stacks.Chow.BivariantChowClass.restrict_comp` — compatibility with the composition of bivariant
  classes: for `a ∈ A^p(X ⟶ Y)`, `b ∈ A^q(Y ⟶ Z)` and `h : Z' ⟶ Z`, `res(a ∘ b) = res(a) ∘ res(b)`,
  up to the canonical isomorphism of the sources.

## References

* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace BivariantChowClass

variable {C : ChowSituation.{u}}

/-- A morphism over the base between schemes locally of finite type over it is locally of finite
type. -/
theorem locallyOfFiniteType_of_structure {S X Y : Scheme.{u}} {sX : X ⟶ S}
    [LocallyOfFiniteType sX] (sY : Y ⟶ S) (f : X ⟶ Y) (hf : f ≫ sY = sX) :
    LocallyOfFiniteType f := by
  have : LocallyOfFiniteType (f ≫ sY) := hf ▸ inferInstance
  exact locallyOfFiniteType_of_comp f sY

/-! ### Cap operations along isomorphisms of test schemes -/

section Cap

variable {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
  [LocallyOfFiniteType sY] {f : X ⟶ Y} {hf : f ≫ sY = sX} {p : ℤ}

/-- The cap operation of a bivariant class is natural for an isomorphism `e` of test schemes over
`Y`: this is condition (1) of Stacks 0B76 for the proper morphism `e`, with the base change of `e`
given by any morphism `w` over `X` and over `e`. -/
theorem cap_chowPushforwardOfIso (c : BivariantChowClass C sX sY f hf p) {T₁ T₂ : Scheme.{u}}
    (g₁ : T₁ ⟶ Y) [LocallyOfFiniteType g₁] (g₂ : T₂ ⟶ Y) [LocallyOfFiniteType g₂] (e : T₂ ⟶ T₁)
    [IsIso e] (he : e ≫ g₁ = g₂) (heY : e ≫ g₁ ≫ sY = g₂ ≫ sY)
    (w : pullback f g₂ ⟶ pullback f g₁) [IsIso w]
    (hw₁ : w ≫ pullback.fst f g₁ = pullback.fst f g₂)
    (hw₂ : w ≫ pullback.snd f g₁ = pullback.snd f g₂ ≫ e)
    (hwX : w ≫ pullback.fst f g₁ ≫ sX = pullback.fst f g₂ ≫ sX) (k : ℤ)
    (α : chowGroup C (g₂ ≫ sY) k) :
    c.cap g₁ k (chowPushforwardOfIso C (g₂ ≫ sY) (g₁ ≫ sY) e heY k α) =
      chowPushforwardOfIso C (pullback.fst f g₂ ≫ sX) (pullback.fst f g₁ ≫ sX) w hwX (k - p)
        (c.cap g₂ k α) := by
  subst he
  obtain rfl : w = bivariantBaseChangeMap f g₁ e :=
    pullback.hom_ext (by simp [hw₁, bivariantBaseChangeMap])
      (by simp [hw₂, bivariantBaseChangeMap])
  exact c.cap_properPushforward g₁ e k α

/-- The cap operations of a bivariant class at two equal test morphisms are carried to one another
by the pushforward along the comparison isomorphism of the two base changes. -/
theorem cap_congr_test (c : BivariantChowClass C sX sY f hf p) {T : Scheme.{u}}
    {g₁ g₂ : T ⟶ Y} [LocallyOfFiniteType g₁] [LocallyOfFiniteType g₂] (e : g₁ = g₂)
    (hbase : (pullback.congrHom (rfl : f = f) e).hom ≫ (pullback.fst f g₂ ≫ sX) =
      pullback.fst f g₁ ≫ sX)
    (k : ℤ) {q : T ⟶ C.S} [LocallyOfFiniteType q] (α : chowGroup C q k) (h₁ : q = g₁ ≫ sY)
    (h₂ : q = g₂ ≫ sY) :
    c.cap g₂ k (chowGroupCongr C h₂ k α) =
      chowPushforwardOfIso C (pullback.fst f g₁ ≫ sX) (pullback.fst f g₂ ≫ sX)
        (pullback.congrHom rfl e).hom hbase (k - p) (c.cap g₁ k (chowGroupCongr C h₁ k α)) := by
  cases e
  rw [chowPushforwardOfIso_congr_apply C (pullback.fst f g₁ ≫ sX) (pullback.fst f g₁ ≫ sX)
    (pullback.congrHom rfl rfl).hom (𝟙 _) (by simp) hbase (Category.id_comp _) (k - p),
    chowPushforwardOfIso_id]

end Cap

/-! ### Transport along an isomorphism of the source -/

section Transport

variable {A B W : Scheme.{u}} {sA : A ⟶ C.S} [LocallyOfFiniteType sA] {sB : B ⟶ C.S}
  [LocallyOfFiniteType sB] {sW : W ⟶ C.S} [LocallyOfFiniteType sW] {v : A ⟶ W}
  {hv : v ≫ sW = sA} {u : B ⟶ W} {p : ℤ}

/-- The transport of a bivariant class `c ∈ A^p(A ⟶ W)` along an isomorphism `θ : A ≅ B` over
`W`: the class of `A^p(B ⟶ W)` whose cap operations are those of `c` read through the induced
isomorphisms `T ×_W A ≅ T ×_W B`. -/
def transport (hu : u ≫ sW = sB) (θ : A ≅ B) (hθ : θ.hom ≫ u = v)
    (c : BivariantChowClass C sA sW v hv p) : BivariantChowClass C sB sW u hu p :=
  haveI := locallyOfFiniteType_of_structure sW v hv
  haveI := locallyOfFiniteType_of_structure sW u hu
  equivBivariantClass.symm (bivariantTransport C (gysinSystemOfInvertible C) sA sB sW v hv u hu
    θ hθ p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (equivBivariantClass c))

/-- The cap operation of a transported class. -/
theorem transport_cap (hu : u ≫ sW = sB) (θ : A ≅ B) (hθ : θ.hom ≫ u = v)
    (c : BivariantChowClass C sA sW v hv p) {T : Scheme.{u}} (g : T ⟶ W) [LocallyOfFiniteType g]
    (k : ℤ) (α : chowGroup C (g ≫ sW) k) :
    (c.transport hu θ hθ).cap g k α =
      chowPushforwardOfIso C (pullback.fst v g ≫ sA) (pullback.fst u g ≫ sB)
        (transportPullbackIso v u θ hθ g).hom
        (transportPullbackIso_hom_comp_base C sA sB sW v hv u hu θ hθ g) (k - p)
        (c.cap g k α) :=
  rfl

end Transport

/-! ### The restriction -/

section Restriction

variable {X Y Y' : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
  [LocallyOfFiniteType sY] {f : X ⟶ Y} {p : ℤ} {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY']

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType sY'] in
/-- The base change `X' = Y' ×_Y X ⟶ Y'` is a morphism over the base. -/
theorem restrict_structure_eq (hf : f ≫ sY = sX) (h : Y' ⟶ Y) (hh : h ≫ sY = sY') :
    pullback.snd f h ≫ sY' = pullback.fst f h ≫ sX := by
  rw [← hh, ← Category.assoc, ← pullback.condition, Category.assoc, hf]

variable {hf : f ≫ sY = sX} (h : Y' ⟶ Y) (hh : h ≫ sY = sY')

/-- The restriction `res(c) ∈ A^p(X' ⟶ Y')`, `X' = Y' ×_Y X`, of a bivariant class `c ∈ A^p(X ⟶ Y)`
along `h : Y' ⟶ Y`: a scheme `Y''` locally of finite type over `Y'` is one over `Y`, and
`res(c) ∩ α'' = c ∩ α''` for `α'' ∈ CH_k(Y'')` (`Stacks.Chow.BivariantChowClass.restrict_cap`). -/
@[stacks 0F9Z "the restriction map A^p(X → Y) → A^p(X' → Y'), c ↦ res(c)"]
def restrict (c : BivariantChowClass C sX sY f hf p) :
    haveI := locallyOfFiniteType_of_structure sY h hh
    BivariantChowClass C (pullback.fst f h ≫ sX) sY' (pullback.snd f h)
      (restrict_structure_eq hf h hh) p := by
  have := locallyOfFiniteType_of_structure sY h hh
  subst hh
  haveI := locallyOfFiniteType_of_structure sY f hf
  exact equivBivariantClass.symm (bivariantRestriction C (gysinSystemOfInvertible C) sX sY f hf h
    p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (equivBivariantClass c))

/-- `res(c) ∩ α'' = c ∩ α''`: for `g : Y'' ⟶ Y'` and `α'' ∈ CH_k(Y'')`, the cap of the restriction
is the cap of `c` at `g ≫ h`, read on `(Y' ×_Y X) ×_{Y'} Y''` through the canonical isomorphism
with `Y'' ×_Y X`. -/
@[stacks 0F9Z "res(c) ∩ α'' = c ∩ α''"]
theorem restrict_cap (c : BivariantChowClass C sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y')
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY') k) :
    haveI := locallyOfFiniteType_of_structure sY h hh
    (c.restrict h hh).cap g k α =
      chowPushforwardOfIso C (pullback.fst f (g ≫ h) ≫ sX)
        (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX))
        (pullbackLeftPullbackSndIso f h g).inv (by simp) (k - p)
        (c.cap (g ≫ h) k (chowGroupCongr C (by rw [Category.assoc, hh]) k α)) := by
  subst hh
  rfl

/-- The restriction map `A^p(X ⟶ Y) ⟶ A^p(X' ⟶ Y')` as a homomorphism of groups. -/
def restrictAddHom [LocallyOfFiniteType f] [LocallyOfFiniteType h] :
    BivariantChowClass C sX sY f hf p →+
      BivariantChowClass C (pullback.fst f h ≫ sX) sY' (pullback.snd f h)
        (restrict_structure_eq hf h hh) p where
  toFun c := c.restrict h hh
  map_zero' := by
    ext T g _ k α
    simp [restrict_cap]
  map_add' c d := by
    ext T g _ k α
    simp [restrict_cap, map_add]

/-- The homomorphism `restrictAddHom h hh` sends a bivariant class `c` to its restriction
`c.restrict h hh`. -/
@[simp]
theorem restrictAddHom_apply [LocallyOfFiniteType f] [LocallyOfFiniteType h]
    (c : BivariantChowClass C sX sY f hf p) : restrictAddHom h hh c = c.restrict h hh :=
  rfl

/-! ### Compatibility with composition of base changes -/

/-- Restriction is compatible with compositions of base changes: restricting `c` along `h : Y' ⟶ Y`
and then along `h' : Y'' ⟶ Y'` is restricting `c` along `h' ≫ h`, the two classes agreeing after
the canonical identification `(X ×_Y Y') ×_{Y'} Y'' ≅ X ×_Y Y''` of their sources. -/
@[stacks 0F9Z "compatibility with compositions: res along Y'' → Y' after res along Y' → Y is \
res along Y'' → Y"]
theorem restrict_restrict {Y'' : Scheme.{u}} {sY'' : Y'' ⟶ C.S} [LocallyOfFiniteType sY'']
    (h' : Y'' ⟶ Y') (hh' : h' ≫ sY' = sY'') (c : BivariantChowClass C sX sY f hf p) :
    haveI := locallyOfFiniteType_of_structure sY h hh
    haveI := locallyOfFiniteType_of_structure sY' h' hh'
    ((c.restrict h hh).restrict h' hh').transport
        (restrict_structure_eq hf (h' ≫ h) (by rw [Category.assoc, hh, hh']))
        (pullbackLeftPullbackSndIso f h h') (pullbackLeftPullbackSndIso_hom_snd f h h') =
      c.restrict (h' ≫ h) (by rw [Category.assoc, hh, hh']) := by
  have := locallyOfFiniteType_of_structure sY h hh
  have := locallyOfFiniteType_of_structure sY' h' hh'
  have := locallyOfFiniteType_of_structure sY f hf
  ext T g _ k α
  rw [transport_cap, restrict_cap, restrict_cap, restrict_cap, chowGroupCongr_chowGroupCongr,
    cap_congr_test c (Category.assoc g h' h) (by simp) k α
      (by rw [Category.assoc, Category.assoc, hh, hh'])
      (by rw [Category.assoc, Category.assoc, hh, hh']),
    chowPushforwardOfIso_comp_apply C _ _ _ (pullbackLeftPullbackSndIso f h (g ≫ h')).inv
      (pullbackLeftPullbackSndIso (pullback.snd f h) h' g).inv,
    chowPushforwardOfIso_comp_apply C _ _ _
      ((pullbackLeftPullbackSndIso f h (g ≫ h')).inv ≫
        (pullbackLeftPullbackSndIso (pullback.snd f h) h' g).inv)
      (transportPullbackIso _ _ (pullbackLeftPullbackSndIso f h h')
        (pullbackLeftPullbackSndIso_hom_snd f h h') g).hom,
    chowPushforwardOfIso_comp_apply C _ _ _
      (pullback.congrHom (rfl : f = f) (Category.assoc g h' h)).hom
      (pullbackLeftPullbackSndIso f (h' ≫ h) g).inv]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ (k - p) _
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_ <;> simp [transportPullbackIso]

end Restriction

/-! ### Composition -/

section Composition

variable {X Y Z : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
  [LocallyOfFiniteType sY] {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {f : X ⟶ Y} {g : Y ⟶ Z}
  {hf : f ≫ sY = sX} {hg : g ≫ sZ = sY} {p q : ℤ}

/-- The composite `a ∘ b ∈ A^{p+q}(X ⟶ Z)` of Stacks 0B75 of `a ∈ A^p(X ⟶ Y)` and `b ∈ A^q(Y ⟶ Z)`:
`(a ∘ b) ∩ α = a ∩ (b ∩ α)` (`Stacks.Chow.BivariantChowClass.comp_cap`). -/
def comp (a : BivariantChowClass C sX sY f hf p) (b : BivariantChowClass C sY sZ g hg q) :
    BivariantChowClass C sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) (p + q) :=
  haveI := locallyOfFiniteType_of_structure sY f hf
  haveI := locallyOfFiniteType_of_structure sZ g hg
  equivBivariantClass.symm (bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q
    (equivBivariantClass a) (equivBivariantClass b))

/-- The cap operation of a composite: cap with `b`, then with `a`, read on `T ×_Z X` through the
canonical isomorphism with `(T ×_Z Y) ×_Y X`, in degree `k - (p + q) = (k - q) - p`. -/
theorem comp_cap (a : BivariantChowClass C sX sY f hf p) (b : BivariantChowClass C sY sZ g hg q)
    {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sZ) k) :
    (a.comp b).cap t k α =
      chowGroupDegreeEquiv C (pullback.fst (f ≫ g) t ≫ sX) (by ring : k - q - p = k - (p + q))
        (chowPushforwardOfIso C (pullback.fst f (pullback.fst g t) ≫ sX)
          (pullback.fst (f ≫ g) t ≫ sX) (pullbackRightPullbackFstIso g t f).hom
          (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t) (k - q - p)
          (a.cap (pullback.fst g t) (k - q) (b.cap t k α))) :=
  rfl

/-- Restriction is compatible with the composition of bivariant classes. For `a ∈ A^p(X ⟶ Y)`,
`b ∈ A^q(Y ⟶ Z)` and `h : Z' ⟶ Z`, write `Y' = Y ×_Z Z'` and `X' = X ×_Y Y' = X ×_Z Z'`; then
`res(a ∘ b) = res(a) ∘ res(b)` in `A^{p+q}(X' ⟶ Z')`, where `res(a) ∈ A^p(X ×_Y Y' ⟶ Y')` is the
restriction along `Y' ⟶ Y` and `res(b) ∈ A^q(Y' ⟶ Z')` the restriction along `h`. The two sources
are identified by the canonical isomorphism `X ×_Y (Y ×_Z Z') ≅ X ×_Z Z'`. -/
@[stacks 0F9Z "compatibility with compositions: res(a ∘ b) = res(a) ∘ res(b)"]
theorem restrict_comp {Z' : Scheme.{u}} {sZ' : Z' ⟶ C.S} [LocallyOfFiniteType sZ'] (h : Z' ⟶ Z)
    (hh : h ≫ sZ = sZ') (a : BivariantChowClass C sX sY f hf p)
    (b : BivariantChowClass C sY sZ g hg q) :
    haveI := locallyOfFiniteType_of_structure sZ h hh
    ((a.restrict (pullback.fst g h) rfl).comp (b.restrict h hh)).transport
        (restrict_structure_eq (comp_comp_structureMorphism_eq hf hg) h hh)
        (pullbackRightPullbackFstIso g h f) (pullbackRightPullbackFstIso_hom_snd g h f) =
      (a.comp b).restrict h hh := by
  have := locallyOfFiniteType_of_structure sZ h hh
  have := locallyOfFiniteType_of_structure sY f hf
  have := locallyOfFiniteType_of_structure sZ g hg
  ext T t _ k α
  rw [transport_cap, comp_cap, restrict_cap, restrict_cap, restrict_cap, comp_cap,
    chowGroupCongr_chowPushforwardOfIso_target C _ _ _ _ (by simp),
    cap_chowPushforwardOfIso a (pullback.fst (pullback.snd g h) t ≫ pullback.fst g h)
      (pullback.fst g (t ≫ h)) (pullbackLeftPullbackSndIso g h t).inv (by simp) (by simp)
      (pullback.map f (pullback.fst g (t ≫ h)) f
        (pullback.fst (pullback.snd g h) t ≫ pullback.fst g h) (𝟙 X)
        (pullbackLeftPullbackSndIso g h t).inv (𝟙 Y) (by simp) (by simp))
      (by simp) (by simp) (by simp)]
  simp only [chowGroupDegreeEquiv_chowPushforwardOfIso, chowPushforwardOfIso_comp_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_ <;> simp [transportPullbackIso]

end Composition

end BivariantChowClass

end Stacks.Chow

end
