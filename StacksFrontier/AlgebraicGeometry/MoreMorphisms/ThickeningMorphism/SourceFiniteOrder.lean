module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Cartesian
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.CartesianDifferentials
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.InfinitesimalNeighbourhood

/-!
# Cartesian morphisms of thickenings of schemes with a finite-order source thickening

Let

```
X --f--→ S
|        |
i        j
↓        ↓
X' -f'-→ S'
```

be a cartesian square of schemes in which `j` is a closed immersion and `i` is a
*finite-order* thickening. Nothing is assumed about the order of `j`. If `I ⊆ 𝒪_{S'}` is the
ideal sheaf of `j`, then the ideal sheaf of `i` is the inverse image of `I`, so if
`(ker i) ^ (n + 1) = 0` then the inverse image of `I ^ (n + 1)` vanishes and `f'` factors
through the closed subscheme `T = V(I ^ (n + 1))` of `S'`. The square stays cartesian with `S'`
replaced by `T`, and now `S ⊂ T` is an `n`th order thickening. This reduces a statement about
a cartesian morphism of thickenings with finite-order *source* thickening to the case of a
finite-order *target* thickening, which is Stacks 09ZW, provided the property in question does
not distinguish `f'` from the morphism `X' ⟶ T` through which it factors.

The properties for which this is carried out are local finite type, local quasi-finiteness
(together with local finite type), unramifiedness and formal unramifiedness, the last of which
is the vanishing of the module of relative differentials. In each case composition with the
closed immersion `T ⟶ S'` neither creates nor destroys the property.

## Main results

* `Stacks.Thickenings.exists_isFiniteOrderThickening_factorization`: the factorisation of `f'`
  through `V(I ^ (n + 1))` and the resulting cartesian square with finite-order target.
* `Stacks.Thickenings.iff_of_isFiniteOrderThickening_source`: a property of morphisms of
  schemes which is invariant under cartesian morphisms of thickenings with finite-order target
  thickening, and unchanged by composition with a closed immersion, is invariant under
  cartesian morphisms of thickenings with finite-order source thickening.
* `Stacks.Thickenings.locallyOfFiniteType_iff_of_isFiniteOrderThickening_source`,
  `Stacks.Thickenings.locallyQuasiFinite_iff_of_isFiniteOrderThickening_source`,
  `Stacks.Thickenings.unramified_iff_of_isFiniteOrderThickening_source` and
  `Stacks.Thickenings.formallyUnramified_iff_of_isFiniteOrderThickening_source`: the four
  instances.

## References

* [Stacks Project, Tag 09ZW](https://stacks.math.columbia.edu/tag/09ZW)
* [Stacks Project, Tag 09ZZ](https://stacks.math.columbia.edu/tag/09ZZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

variable {X X' S S' : Scheme.{u}}

/-- **Reduction to a finite-order target thickening.** In a cartesian square `(i, f, f', j)` of
schemes whose right vertical map `j` is a closed immersion and whose left vertical map `i` is a
finite-order thickening, the ambient morphism `f'` factors through a closed immersion
`k : T ⟶ S'` through which `j` factors as well, in such a way that the square with `k` removed is
still cartesian and its right vertical map `S ⟶ T` is a finite-order thickening.

Here `T` is the closed subscheme cut out by `I ^ (n + 1)`, where `I` is the ideal sheaf of `j`
and `(ker i) ^ (n + 1) = 0`: the ideal sheaf of `i` is the inverse image of `I`, so the inverse
image of `I ^ (n + 1)` vanishes, which is what it means for `f'` to factor through `T`. -/
theorem exists_isFiniteOrderThickening_factorization (i : X ⟶ X') (j : S ⟶ S') (f : X ⟶ S)
    (f' : X' ⟶ S') (hi : IsFiniteOrderThickening i) (hj : IsClosedImmersion j)
    (hcart : IsPullback i f f' j) :
    ∃ (T : Scheme.{u}) (k : T ⟶ S') (j₀ : S ⟶ T) (f₀ : X' ⟶ T),
      IsClosedImmersion k ∧ j₀ ≫ k = j ∧ f₀ ≫ k = f' ∧ IsFiniteOrderThickening j₀ ∧
        IsPullback i f f₀ j₀ := by
  obtain ⟨n, hn⟩ := hi.2
  set I := j.ker
  -- The ideal sheaf of `i` is the inverse image of that of `j`.
  have hiker : i.ker = I.comap f' := by
    rw [← hcart.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have hcomap : (I ^ (n + 1)).comap f' = ⊥ := by
    rw [Stacks.IdealSheaf.comap_pow, ← hiker, hn]
  let k := (I ^ (n + 1)).subschemeι
  -- `f'` factors through `T = V(I ^ (n + 1))`.
  have hf'ker : k.ker ≤ f'.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.map_bot,
      Scheme.IdealSheafData.le_map_iff_comap_le, hcomap]
  let f₀ := IsClosedImmersion.lift k f' hf'ker
  have hf₀ : f₀ ≫ k = f' := IsClosedImmersion.lift_fac k f' hf'ker
  -- `j` factors through `T` as `S ≅ V(I) ⟶ V(I ^ (n + 1))`.
  let c := Scheme.IdealSheafData.inclusion (Stacks.IdealSheaf.pow_succ_le_self I n)
  let j₀ := j.toImage ≫ c
  have hj₀ : j₀ ≫ k = j := by
    simp only [j₀, c, k, Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
    exact j.toImage_imageι
  have hcorder : IsNthOrderThickening n c := Stacks.IdealSheaf.isNthOrderThickening_inclusion I n
  have hj₀order : IsFiniteOrderThickening j₀ := by
    have : IsClosedImmersion c := hcorder.1
    refine ⟨inferInstance, n, ?_⟩
    rw [Scheme.Hom.ker_comp_of_isIso]
    exact hcorder.2
  -- The square with `k` removed is cartesian, because `k` is a monomorphism.
  have hright : IsPullback j₀ (𝟙 S) k j :=
    IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, hj₀]⟩
  have hw : i ≫ f₀ = f ≫ j₀ := by
    rw [← cancel_mono k, Category.assoc, hf₀, hcart.w, Category.assoc, hj₀]
  exact ⟨_, k, j₀, f₀, inferInstance, hj₀, hf₀, hj₀order,
    .of_bot (by simpa only [Category.comp_id, hf₀] using hcart) hw hright⟩

/-- **Finite order on the source suffices.** Let `P` be a property of morphisms of schemes which
is invariant under every cartesian morphism of thickenings whose target thickening has finite
order (the shape of Stacks 09ZW), and which is unchanged by composing with a closed immersion.
Then `P` is invariant under every cartesian square `(i, f, f', j)` with `i` a finite-order
thickening and `j` a closed immersion. -/
theorem iff_of_isFiniteOrderThickening_source (P : MorphismProperty Scheme.{u})
    (hP : ∀ {X X' S S' : Scheme.{u}} (i : X ⟶ X') (j : S ⟶ S') (f : X ⟶ S) (f' : X' ⟶ S'),
      IsFiniteOrderThickening i → IsFiniteOrderThickening j → IsPullback i f f' j →
        (P f ↔ P f'))
    (hcomp : ∀ {A T S' : Scheme.{u}} (g : A ⟶ T) (k : T ⟶ S'), IsClosedImmersion k →
      (P (g ≫ k) ↔ P g))
    (i : X ⟶ X') (j : S ⟶ S') (f : X ⟶ S) (f' : X' ⟶ S') (hi : IsFiniteOrderThickening i)
    (hj : IsClosedImmersion j) (hcart : IsPullback i f f' j) : P f ↔ P f' := by
  obtain ⟨T, k, j₀, f₀, hk, -, hf₀, hj₀, hsq⟩ :=
    exists_isFiniteOrderThickening_factorization i j f f' hi hj hcart
  rw [← hf₀, hcomp f₀ k hk]
  exact hP i j₀ f f₀ hi hj₀ hsq

/-- **Stacks 09ZW, part (2), with finite order on the source.** In a cartesian square
`(i, f, f', j)` of schemes with `i` a finite-order thickening and `j` a closed immersion, `f` is
locally of finite type exactly when `f'` is. -/
theorem locallyOfFiniteType_iff_of_isFiniteOrderThickening_source (i : X ⟶ X') (j : S ⟶ S')
    (f : X ⟶ S) (f' : X' ⟶ S') (hi : IsFiniteOrderThickening i) (hj : IsClosedImmersion j)
    (hcart : IsPullback i f f' j) : LocallyOfFiniteType f ↔ LocallyOfFiniteType f' :=
  iff_of_isFiniteOrderThickening_source @LocallyOfFiniteType
    (fun i j f f' _ hj hcart =>
      locallyOfFiniteType_iff_of_isFiniteOrderThickening i j f f' hj hcart)
    (fun g k _ => ⟨fun _ => locallyOfFiniteType_of_comp g k, fun _ => inferInstance⟩)
    i j f f' hi hj hcart

/-- **Stacks 09ZW, part (3), with finite order on the source.** In a cartesian square
`(i, f, f', j)` of schemes with `i` a finite-order thickening and `j` a closed immersion, `f` is
locally of finite type and locally quasi-finite exactly when `f'` is. -/
theorem locallyQuasiFinite_iff_of_isFiniteOrderThickening_source (i : X ⟶ X') (j : S ⟶ S')
    (f : X ⟶ S) (f' : X' ⟶ S') (hi : IsFiniteOrderThickening i) (hj : IsClosedImmersion j)
    (hcart : IsPullback i f f' j) :
    (LocallyOfFiniteType f ∧ LocallyQuasiFinite f) ↔
      (LocallyOfFiniteType f' ∧ LocallyQuasiFinite f') :=
  iff_of_isFiniteOrderThickening_source (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite)
    (fun i j f f' hi hj hcart =>
      locallyQuasiFinite_iff_of_isFiniteOrderThickening i j f f' hi.isThickening hj hcart)
    (fun g k _ => ⟨fun ⟨_, _⟩ => ⟨locallyOfFiniteType_of_comp g k, LocallyQuasiFinite.of_comp g k⟩,
      fun ⟨_, _⟩ => ⟨inferInstanceAs (LocallyOfFiniteType (g ≫ k)),
        inferInstanceAs (LocallyQuasiFinite (g ≫ k))⟩⟩)
    i j f f' hi hj hcart

/-- **Stacks 09ZW, part (5), with finite order on the source.** In a cartesian square
`(i, f, f', j)` of schemes with `i` a finite-order thickening and `j` a closed immersion, `f` is
formally unramified (its module of relative differentials vanishes) exactly when `f'` is. -/
theorem formallyUnramified_iff_of_isFiniteOrderThickening_source (i : X ⟶ X') (j : S ⟶ S')
    (f : X ⟶ S) (f' : X' ⟶ S') (hi : IsFiniteOrderThickening i) (hj : IsClosedImmersion j)
    (hcart : IsPullback i f f' j) : FormallyUnramified f ↔ FormallyUnramified f' :=
  iff_of_isFiniteOrderThickening_source @FormallyUnramified
    (fun i j f f' _ hj hcart => formallyUnramified_iff_of_isFiniteOrderThickening i j f f' hj hcart)
    (fun g k _ => ⟨fun _ => FormallyUnramified.of_comp g k, fun hg =>
        MorphismProperty.comp_mem _ g k hg (formallyUnramified_of_unramified k)⟩)
    i j f f' hi hj hcart

/-- **Stacks 09ZW, part (6), with finite order on the source.** In a cartesian square
`(i, f, f', j)` of schemes with `i` a finite-order thickening and `j` a closed immersion, `f` is
unramified exactly when `f'` is. -/
theorem unramified_iff_of_isFiniteOrderThickening_source (i : X ⟶ X') (j : S ⟶ S')
    (f : X ⟶ S) (f' : X' ⟶ S') (hi : IsFiniteOrderThickening i) (hj : IsClosedImmersion j)
    (hcart : IsPullback i f f' j) : Unramified f ↔ Unramified f' := by
  simp only [unramified_iff_locallyOfFiniteType_and_formallyUnramified]
  exact and_congr (locallyOfFiniteType_iff_of_isFiniteOrderThickening_source i j f f' hi hj hcart)
    (formallyUnramified_iff_of_isFiniteOrderThickening_source i j f f' hi hj hcart)

end Stacks.Thickenings

end
