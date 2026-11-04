module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescentLift
import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinNaturality

/-!
# The proper pushforward `f_* ∘ c` at the Gysin system of an invertible module: algebra and
functoriality

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` be proper
and `g : Y ⟶ Z` locally of finite type over `S`. For a bivariant class `c ∈ A^p(X ⟶ Z)` for
`f ≫ g` against the Gysin system `Stacks.Chow.gysinSystemOfInvertible`, the class
`f_* ∘ c ∈ A^p(Y ⟶ Z)` of Stacks 0EPK is `Stacks.Chow.bivariantProperPushforwardOfInvertible`.
This file proves how it interacts with the group structure, with identities and composites of
proper morphisms, and with the composition of Stacks 0B75.

## Main definitions

* `Stacks.Chow.bivariantProperPushforwardOfInvertibleAddHom` — `c ↦ f_* ∘ c` as a homomorphism
  of groups.
* `Stacks.Chow.BivariantClass.congrHom` — a bivariant class for a morphism read as one for an
  equal morphism, such as `(f ≫ g) ≫ h` and `f ≫ (g ≫ h)`.

## Main results

* `Stacks.Chow.bivariantProperPushforwardOfInvertible_cap` — the cap operation of `f_* ∘ c` is
  `α ↦ f'_*(c ∩ α)`.
* `Stacks.Chow.bivariantProperPushforwardOfInvertible_add` —
  `f_* ∘ (c + c') = f_* ∘ c + f_* ∘ c'`.
* `Stacks.Chow.bivariantProperPushforwardOfInvertible_id`,
  `Stacks.Chow.bivariantProperPushforwardOfInvertible_comp` — `(𝟙 Y)_* ∘ c = c` and
  `(f₁ ≫ f₂)_* ∘ c = f₂_* ∘ (f₁_* ∘ c)`, from the functoriality of proper pushforward on Chow
  groups (Stacks 02R5).
* `Stacks.Chow.bivariantProperPushforwardOfInvertible_bivariantCompositeOfInvertible` —
  `f_* ∘ (c ∘ d) = (f_* ∘ c) ∘ d` for the composition of Stacks 0B75.

## References

* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Class

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [IsProper f]
  (g : Y ⟶ Z) [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (p : ℤ)

/-- The cap operation of `f_* ∘ c` is `α ↦ f'_*(c ∩ α)`. -/
@[simp]
theorem bivariantProperPushforwardOfInvertible_cap
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) p)
    {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sZ) k) :
    (bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p c).cap t k α =
      bivariantProperPushforwardCap C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
        (properPushforwardDescends C) p c t k α :=
  rfl

/-- A bivariant class capping by the rule of Stacks 0EPK is `f_* ∘ c`. -/
theorem eq_bivariantProperPushforwardOfInvertible_of_isBivariantProperPushforward
    {c : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) p}
    {d : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg p}
    (hd : IsBivariantProperPushforward C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
      (properPushforwardDescends C) p c d) :
    d = bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p c :=
  eq_of_isBivariantProperPushforward (hpp := properPushforwardDescends C) hd
    (isBivariantProperPushforward_bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p c)

/-- Proper pushforward of bivariant classes is additive:
`f_* ∘ (c + c') = f_* ∘ c + f_* ∘ c'`. -/
theorem bivariantProperPushforwardOfInvertible_add
    (c c' : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) p) :
    bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p (c + c') =
      bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p c +
        bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p c' :=
  (eq_bivariantProperPushforwardOfInvertible_of_isBivariantProperPushforward C sX sY sZ f g hf hg p
    (IsBivariantProperPushforward.add (hpp := properPushforwardDescends C)
      (isBivariantProperPushforward_bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p c)
      (isBivariantProperPushforward_bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p
        c'))).symm

/-- Proper pushforward of bivariant classes commutes with negation. -/
theorem bivariantProperPushforwardOfInvertible_neg
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) p) :
    bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p (-c) =
      -bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p c :=
  (eq_bivariantProperPushforwardOfInvertible_of_isBivariantProperPushforward C sX sY sZ f g hf hg p
    (IsBivariantProperPushforward.neg (hpp := properPushforwardDescends C)
      (isBivariantProperPushforward_bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p
        c))).symm

/-- The proper pushforward of the zero bivariant class is zero. -/
theorem bivariantProperPushforwardOfInvertible_zero :
    bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p 0 = 0 :=
  (eq_bivariantProperPushforwardOfInvertible_of_isBivariantProperPushforward C sX sY sZ f g hf hg p
    (IsBivariantProperPushforward.zero (hpp := properPushforwardDescends C))).symm

/-- Proper pushforward of bivariant classes commutes with subtraction. -/
theorem bivariantProperPushforwardOfInvertible_sub
    (c c' : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) p) :
    bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p (c - c') =
      bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p c -
        bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p c' :=
  (eq_bivariantProperPushforwardOfInvertible_of_isBivariantProperPushforward C sX sY sZ f g hf hg p
    (IsBivariantProperPushforward.sub (hpp := properPushforwardDescends C)
      (isBivariantProperPushforward_bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p c)
      (isBivariantProperPushforward_bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p
        c'))).symm

/-- **Stacks 0EPK.** Proper pushforward `c ↦ f_* ∘ c` as a homomorphism of groups
`A^p(X ⟶ Z) ⟶ A^p(Y ⟶ Z)`. -/
def bivariantProperPushforwardOfInvertibleAddHom :
    BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
        (comp_comp_structureMorphism_eq hf hg) p →+
      BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg p where
  toFun := bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p
  map_zero' := bivariantProperPushforwardOfInvertible_zero C sX sY sZ f g hf hg p
  map_add' := bivariantProperPushforwardOfInvertible_add C sX sY sZ f g hf hg p

/-- The homomorphism of Stacks 0EPK is `c ↦ f_* ∘ c`. -/
@[simp]
theorem bivariantProperPushforwardOfInvertibleAddHom_apply
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) p) :
    bivariantProperPushforwardOfInvertibleAddHom C sX sY sZ f g hf hg p c =
      bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p c :=
  rfl

end Class


/-! ### Transport along an equality of morphisms -/

section CongrHom

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f f' : X ⟶ Y}
  [LocallyOfFiniteType f] [LocallyOfFiniteType f'] {hf : f ≫ sY = sX} {p : ℤ}

/-- A bivariant class for `f : X ⟶ Y`, read as a class for a morphism `f'` equal to `f`. -/
def BivariantClass.congrHom (e : f = f') (hf' : f' ≫ sY = sX)
    (c : BivariantClass C G sX sY f hf p) : BivariantClass C G sX sY f' hf' p := by
  subst e
  exact c

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType f]
  [LocallyOfFiniteType f'] in
/-- The comparison `T ×_Y X ≅ T ×_Y X` of the base changes of two equal morphisms lies over the
base. -/
theorem pullback_congrHom_hom_comp_fst_comp (e : f = f') {T : Scheme.{u}} (t : T ⟶ Y) :
    (pullback.congrHom e rfl).hom ≫ (pullback.fst f' t ≫ sX) = pullback.fst f t ≫ sX := by
  simp

/-- The cap operation of a bivariant class read for an equal morphism is that of the class,
carried along the comparison of the two base changes. -/
theorem BivariantClass.congrHom_cap (e : f = f') (hf' : f' ≫ sY = sX)
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ sY) k) :
    (c.congrHom e hf').cap t k α =
      chowPushforwardOfIso C (pullback.fst f t ≫ sX) (pullback.fst f' t ≫ sX)
        (pullback.congrHom e rfl).hom (pullback_congrHom_hom_comp_fst_comp e t) (k - p)
        (c.cap t k α) := by
  subst e
  rw [chowPushforwardOfIso_congr_apply C (pullback.fst f t ≫ sX) (pullback.fst f t ≫ sX)
    (pullback.congrHom rfl rfl).hom (𝟙 _) (by simp) _ (Category.id_comp _) (k - p),
    chowPushforwardOfIso_id]
  rfl

end CongrHom

/-! ### Functoriality of `f_* ∘ c` -/

/-- Compatibility with the structure morphism of a composite of three maps, from that of the two
last and of the first one. -/
private theorem comp_comp_eq_of_comp_eq {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (u : C ⟶ D)
    {v : B ⟶ D} {w : A ⟶ D} (h₁ : b ≫ u = v) (h₂ : a ≫ v = w) : (a ≫ b) ≫ u = w := by
  rw [Category.assoc, h₁, h₂]

section Functoriality

variable (C : ChowSituation.{u}) {X Y Y' Z : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY'] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]

/-- Pushforward along the identity: `(𝟙 Y)_* ∘ c = c`, for `c ∈ A^p(Y ⟶ Z)` read as a class for
`𝟙 Y ≫ g`. -/
theorem bivariantProperPushforwardOfInvertible_id (g : Y ⟶ Z) [LocallyOfFiniteType g]
    (hg : g ≫ sZ = sY)
    (p : ℤ) (c : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg p) :
    bivariantProperPushforwardOfInvertible C sY sY sZ (𝟙 Y) g (Category.id_comp sY) hg p
        (c.congrHom (Category.id_comp g).symm
          (comp_comp_structureMorphism_eq (Category.id_comp sY) hg)) = c := by
  refine BivariantClass.ext C _ sY sZ g hg p fun t _ k α ↦ ?_
  rw [bivariantProperPushforwardOfInvertible_cap, bivariantProperPushforwardCap_apply,
    BivariantClass.congrHom_cap]
  have hmor : (pullback.congrHom (Category.id_comp g).symm rfl).hom ≫
      bivariantPushforwardBaseChange (𝟙 Y) g t = 𝟙 (pullback g t) := by
    refine pullback.hom_ext ?_ ?_ <;> simp
  refine (chowPush_chowPushforwardOfIso C _ _ _ _ _ _ _ (by rw [Category.assoc,
    bivariantPushforwardBaseChange_comp_structure (Category.id_comp sY) g t,
    pullback_congrHom_hom_comp_fst_comp]) (k - p) (c.cap t k α)).trans ?_
  rw [chowPush_congr C _ _ hmor _ (Category.id_comp _), chowPush_id]

/-- Pushforward along a composite: `(f₁ ≫ f₂)_* ∘ c = f₂_* ∘ (f₁_* ∘ c)` for proper
`f₁ : X ⟶ Y` and `f₂ : Y ⟶ Y'`, the class `c` for `(f₁ ≫ f₂) ≫ g` being read as a class for
`f₁ ≫ (f₂ ≫ g)` on the right. -/
theorem bivariantProperPushforwardOfInvertible_comp (f₁ : X ⟶ Y) [IsProper f₁] (f₂ : Y ⟶ Y')
    [IsProper f₂]
    (g : Y' ⟶ Z) [LocallyOfFiniteType g] (hf₁ : f₁ ≫ sY = sX) (hf₂ : f₂ ≫ sY' = sY)
    (hg : g ≫ sZ = sY') (p : ℤ)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sZ ((f₁ ≫ f₂) ≫ g)
      (comp_comp_structureMorphism_eq (comp_comp_structureMorphism_eq hf₁ hf₂) hg) p) :
    bivariantProperPushforwardOfInvertible C sX sY' sZ (f₁ ≫ f₂) g
        (comp_comp_structureMorphism_eq hf₁ hf₂) hg p c =
      bivariantProperPushforwardOfInvertible C sY sY' sZ f₂ g hf₂ hg p
        (bivariantProperPushforwardOfInvertible C sX sY sZ f₁ (f₂ ≫ g) hf₁
          (comp_comp_structureMorphism_eq hf₂ hg) p
          (c.congrHom (Category.assoc f₁ f₂ g)
            (comp_comp_structureMorphism_eq hf₁ (comp_comp_structureMorphism_eq hf₂ hg)))) := by
  refine BivariantClass.ext C _ sY' sZ g hg p fun t _ k α ↦ ?_
  simp only [bivariantProperPushforwardOfInvertible_cap, bivariantProperPushforwardCap_apply,
    BivariantClass.congrHom_cap]
  have hmor : (pullback.congrHom (Category.assoc f₁ f₂ g) rfl).hom ≫
      bivariantPushforwardBaseChange f₁ (f₂ ≫ g) t ≫ bivariantPushforwardBaseChange f₂ g t =
        bivariantPushforwardBaseChange (f₁ ≫ f₂) g t := by
    refine pullback.hom_ext ?_ ?_ <;> simp
  have hu := pullback_congrHom_hom_comp_fst_comp (sX := sX) (Category.assoc f₁ f₂ g) t
  have hv := bivariantPushforwardBaseChange_comp_structure hf₁ (f₂ ≫ g) t
  have hw := bivariantPushforwardBaseChange_comp_structure hf₂ g t
  have hvw := comp_comp_eq_of_comp_eq _ _ _ hw hv
  have huvw := comp_comp_eq_of_comp_eq _ _ _ hvw hu
  exact ((properChowPushforward_comp₃_apply C (pullback.fst ((f₁ ≫ f₂) ≫ g) t ≫ sX)
    (pullback.fst (f₁ ≫ f₂ ≫ g) t ≫ sX) (pullback.fst (f₂ ≫ g) t ≫ sY)
    (pullback.fst g t ≫ sY') (pullback.congrHom (Category.assoc f₁ f₂ g) rfl).hom
    (bivariantPushforwardBaseChange f₁ (f₂ ≫ g) t) (bivariantPushforwardBaseChange f₂ g t)
    hu hv hw hvw huvw (k - p)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (c.cap t k α)).symm.trans
    (chowPush_congr C _ _ hmor huvw _ (k - p) (c.cap t k α))).symm


/-- **Stacks 0EPK, compatibility with composition.** For `f : X ⟶ Y` proper, `g : Y ⟶ Y'`,
`h : Y' ⟶ Z`, `c ∈ A^p(X ⟶ Y')` and `d ∈ A^q(Y' ⟶ Z)`, pushing forward the composite of
Stacks 0B75 is composing the pushforward: `f_* ∘ (c ∘ d) = (f_* ∘ c) ∘ d` in `A^{p+q}(Y ⟶ Z)`,
the composite `c ∘ d`, a class for `(f ≫ g) ≫ h`, being read as a class for `f ≫ (g ≫ h)`. -/
theorem bivariantProperPushforwardOfInvertible_bivariantCompositeOfInvertible (f : X ⟶ Y)
    [IsProper f]
    (g : Y ⟶ Y') [LocallyOfFiniteType g] (h : Y' ⟶ Z) [LocallyOfFiniteType h]
    (hf : f ≫ sY = sX) (hg : g ≫ sY' = sY) (hh : h ≫ sZ = sY') (p q : ℤ)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY' (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) p)
    (d : BivariantClass C (gysinSystemOfInvertible C) sY' sZ h hh q) :
    bivariantProperPushforwardOfInvertible C sX sY sZ f (g ≫ h) hf
        (comp_comp_structureMorphism_eq hg hh) (p + q)
        ((bivariantCompositeOfInvertible C sX sY' sZ (f ≫ g) h
          (comp_comp_structureMorphism_eq hf hg) hh p q c d).congrHom (Category.assoc f g h)
          (comp_comp_structureMorphism_eq hf (comp_comp_structureMorphism_eq hg hh))) =
      bivariantCompositeOfInvertible C sY sY' sZ g h hg hh p q
        (bivariantProperPushforwardOfInvertible C sX sY sY' f g hf hg p c) d := by
  refine BivariantClass.ext C _ sY sZ (g ≫ h) (comp_comp_structureMorphism_eq hg hh) (p + q)
    fun t _ k α ↦ ?_
  have h₁ := isBivariantClassComposition_bivariantCompositeOfInvertible C sX sY' sZ (f ≫ g) h
    (comp_comp_structureMorphism_eq hf hg) hh p q c d t k α
  have h₂ := isBivariantClassComposition_bivariantCompositeOfInvertible C sY sY' sZ g h hg hh p q
    (bivariantProperPushforwardOfInvertible C sX sY sY' f g hf hg p c) d t k α
  simp only [bivariantProperPushforwardOfInvertible_cap, bivariantProperPushforwardCap_apply,
    BivariantClass.congrHom_cap]
  refine eq_of_heq ((heq_map_index (by ring : k - (p + q) = (k - q) - p) h₁ fun n x =>
    properChowPushforward C (pullback.fst (f ≫ g ≫ h) t ≫ sX) (pullback.fst (g ≫ h) t ≫ sY)
      (bivariantPushforwardBaseChange f (g ≫ h) t)
      (bivariantPushforwardBaseChange_comp_structure hf (g ≫ h) t) n
      (properPushforwardDescends C _ _ _ _ _)
      (chowPushforwardOfIso C (pullback.fst ((f ≫ g) ≫ h) t ≫ sX)
        (pullback.fst (f ≫ g ≫ h) t ≫ sX) (pullback.congrHom (Category.assoc f g h) rfl).hom
        (pullback_congrHom_hom_comp_fst_comp (Category.assoc f g h) t) n x)).trans
    (HEq.trans (heq_of_eq ?_) h₂.symm))
  simp only [bivariantCompositeCap_apply, bivariantProperPushforwardOfInvertible_cap,
    bivariantProperPushforwardCap_apply]
  have hmor : (pullbackRightPullbackFstIso h t (f ≫ g)).hom ≫
      (pullback.congrHom (Category.assoc f g h) rfl).hom ≫
        bivariantPushforwardBaseChange f (g ≫ h) t =
      bivariantPushforwardBaseChange f g (pullback.fst h t) ≫
        (pullbackRightPullbackFstIso h t g).hom := by
    refine pullback.hom_ext ?_ ?_ <;> simp
  have hu := pullbackRightPullbackFstIso_hom_comp_fst_comp sX (f ≫ g) h t
  have hv := pullback_congrHom_hom_comp_fst_comp (sX := sX) (Category.assoc f g h) t
  have hw := bivariantPushforwardBaseChange_comp_structure hf (g ≫ h) t
  have hvw := comp_comp_eq_of_comp_eq _ _ _ hw hv
  have huvw := comp_comp_eq_of_comp_eq _ _ _ hvw hu
  have hx := bivariantPushforwardBaseChange_comp_structure hf g (pullback.fst h t)
  have hy := pullbackRightPullbackFstIso_hom_comp_fst_comp sY g h t
  have hxy := comp_comp_eq_of_comp_eq _ _ _ hy hx
  set x := c.cap (pullback.fst h t) (k - q) (d.cap t k α)
  exact ((properChowPushforward_comp₃_apply C (pullback.fst (f ≫ g) (pullback.fst h t) ≫ sX)
    (pullback.fst ((f ≫ g) ≫ h) t ≫ sX) (pullback.fst (f ≫ g ≫ h) t ≫ sX)
    (pullback.fst (g ≫ h) t ≫ sY) (pullbackRightPullbackFstIso h t (f ≫ g)).hom
    (pullback.congrHom (Category.assoc f g h) rfl).hom
    (bivariantPushforwardBaseChange f (g ≫ h) t) hu hv hw hvw huvw (k - q - p)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) x).symm.trans
    (chowPush_congr C _ _ hmor huvw hxy (k - q - p) x)).trans
    (properChowPushforward_comp_apply C _ _ _
      (bivariantPushforwardBaseChange f g (pullback.fst h t))
      (pullbackRightPullbackFstIso h t g).hom _ rfl hx hy hxy (k - q - p)
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _) x)

end Functoriality

end Stacks.Chow

end
