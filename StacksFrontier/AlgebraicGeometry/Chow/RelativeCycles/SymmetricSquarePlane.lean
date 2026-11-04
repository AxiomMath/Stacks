module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.InvolutionQuotientFactor
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SectionCycle
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SymmetricSquarePlaneField
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BirationalSections
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Zero-cycles of degree two on the plane in characteristic two

Let `k` be a field of characteristic `2`, let `X = A²_k = Spec k[u, v]` over `S = Spec k` and let
`W = X ×_S X = Spec k[u₁, u₂, v₁, v₂]`. Over `W` there is a canonical relative `0`-cycle
`α ∈ z^eff(X_W/W, 0)`, with `α_w = [x₁] + [x₂]` for `w = (x₁, x₂)`, invariant under the involution
`σ` exchanging the factors. The quotient `Sym²(X) = W/⟨σ⟩` is the spectrum of
`B = k[u₁ + u₂, u₁u₂, v₁ + v₂, v₁v₂, u₁v₁ + u₂v₂]`, and the image of the diagonal in it is
`V = Spec k[u₁², v₁²]`. Stacks Remark 0H5Y observes that `α` does not descend to `Sym²(X)`:
at the generic point `η` of `V` a cycle `β_η` would be a `0`-cycle on `A²_{k(u₁², v₁²)}` whose
pullback to `A²_{k(u₁, v₁)}` is twice the point `(u₁, v₁)`, which is impossible. Consequently the
functor `S' ↦ z^eff(S' ×_S X / S', 0)` is not representable on the category of weakly normal
schemes of finite type over `k`: a representing object `M` would turn `α` into a `σ`-invariant
morphism `W ⟶ M`, which factors through `Sym²(X)` and produces such a `β`.

## Main definitions

* `Stacks.Chow.SymPlane.alpha` — the cycle `α`, the sum of the pullbacks of the diagonal cycle of
  `X/S` along the two projections `W ⟶ X`.
* `Stacks.Chow.SymPlane.quot` — the quotient morphism `W ⟶ Sym²(X)`.
* `Stacks.Chow.SymPlane.weaklyNormalOfFiniteType` — the weakly normal schemes of finite type
  over `k`.

## Main results

* `Stacks.Chow.SymPlane.map_swapHom_alpha` — `α` is `σ`-invariant.
* `Stacks.Chow.SymPlane.map_sym_diagonalRestriction` — the image of the diagonal is
  `Spec k[u², v²]`.
* `Stacks.Chow.SymPlane.baseChange_quot_ne_alpha` — no family of `0`-cycles on
  `X ×_S Sym²(X) / Sym²(X)` pulls back to `α`.
* `Stacks.Chow.SymPlane.not_isRepresentable_of_le` — the functor is not representable on any full
  subcategory of the schemes of finite type over `k` containing `W` and the principal opens of `W`
  and of `Sym²(X)`.
* `Stacks.Chow.SymPlane.not_isRepresentable_weaklyNormal` — in particular it is not representable
  on the weakly normal schemes of finite type over `k`, a scheme being weakly normal when every
  birational universal homeomorphism onto it has a section.
* `Stacks.Chow.SymPlane.not_isRepresentable` — nor on all schemes locally of finite type over
  `k`.

## Implementation notes

The impossibility at `η` is detected after a further base change to the generic point
`Spec k(u, v) ⟶ W` of the diagonal, where the base change of `β` factors through
`Spec k(u², v²) ⟶ Sym²(X)`: the extension `k(u, v)/k(u², v²)` has degree at least `3`
(`Stacks.Chow.SymPlane.three_le_finrank_squareField`), and base change of a `0`-cycle along a
finite extension of degree `d` multiplies the coefficient of a rational point by `d`
(`Stacks.Chow.finrank_dvd_of_baseChangeFamilyOfIsPullback_eq_single`), while the base change of
`α` is `2 [(u, v)]`. Since `2` is not divisible by `d ≥ 3` no `β` exists, and the argument applies
to `β` over any open neighbourhood of `η`.

The descent of a `σ`-invariant morphism `W ⟶ M` is only needed near `η`, which is fixed by `σ`;
there it is `AlgebraicGeometry.exists_factor_specAway_of_comp_eq`, using that `B` is the ring of
invariants (`Stacks.Chow.SymPlane.mem_sym_iff`). The category in the non-representability
statement is therefore only required to contain `W` and the principal opens of `W` and of
`Sym²(X)`. These are spectra of integrally closed domains, `W` because its ring is a polynomial
ring and `Sym²(X)` because its ring is the ring of invariants of an involution of an integrally
closed domain, and the spectrum of an integrally closed domain is weakly normal
(`AlgebraicGeometry.Scheme.hasBirationalUniversalHomeomorphismSections_spec`).

## References

* [Stacks Project, Remark 0H5Y](https://stacks.math.columbia.edu/tag/0H5Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial

universe u

namespace Stacks.Chow.SymPlane

variable (k : Type u) [Field k]

/-! ### The plane, its square and the symmetric square -/

/-- The plane `X = A²_k = Spec k[u, v]` over `S = Spec k`. -/
abbrev planeHom : Spec (.of (MvPolynomial (Fin 2) k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 2) k)))

/-- The plane `A²_k` is locally of finite type over `Spec k`. -/
instance : LocallyOfFiniteType (planeHom k) :=
  locallyOfFiniteType_specMap_algebraMap _ _

/-- `W = X ×_S X = Spec k[u₁, u₂, v₁, v₂]`. -/
abbrev squareHom : Spec (.of (ring k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (ring k)))

/-- The square `X ×_S X = Spec k[u₁, u₂, v₁, v₂]` is locally of finite type over `Spec k`. -/
instance : LocallyOfFiniteType (squareHom k) :=
  locallyOfFiniteType_specMap_algebraMap _ _

/-- `X`, as an object of the category of schemes locally of finite type over `S`. -/
abbrev planeObj : LocallyOfFiniteTypeOver (Spec (.of k)) := objOf (planeHom k)

/-- `W`, as an object of the category of schemes locally of finite type over `S`. -/
abbrev squareObj : LocallyOfFiniteTypeOver (Spec (.of k)) := objOf (squareHom k)

/-- A morphism of spectra induced by a `k`-algebra map, as a morphism over `Spec k`. -/
def specOverHom {C D : Type u} [CommRing C] [CommRing D] [Algebra k C] [Algebra k D]
    (φ : C →ₐ[k] D) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k D))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k C))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact φ.commutes c)

/-- The underlying morphism of schemes of `specOverHom k φ` is `Spec.map φ`. -/
theorem specOverHom_left {C D : Type u} [CommRing C] [CommRing D] [Algebra k C] [Algebra k D]
    (φ : C →ₐ[k] D) : (specOverHom k φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl

/-- `specOverHom` is contravariantly functorial: `Spec ψ ≫ Spec φ = Spec (ψ ∘ φ)`. -/
theorem specOverHom_comp {C D E : Type u} [CommRing C] [CommRing D] [CommRing E] [Algebra k C]
    [Algebra k D] [Algebra k E] (φ : C →ₐ[k] D) (ψ : D →ₐ[k] E) :
    specOverHom k ψ ≫ specOverHom k φ = specOverHom k (ψ.comp φ) := by
  ext : 1
  simp only [Over.comp_left, specOverHom_left, ← Spec.map_comp]
  rfl

/-- The `j`-th factor `k[u, v] → k[u₁, u₂, v₁, v₂]`. -/
def factorMap (j : Fin 2) : MvPolynomial (Fin 2) k →ₐ[k] ring k := aeval fun i => X (i, j)

/-- The `j`-th projection `W ⟶ X`. -/
def proj (j : Fin 2) : squareObj k ⟶ planeObj k :=
  ObjectProperty.homMk (specOverHom k (factorMap k j))

/-- The involution `σ : W ⟶ W` exchanging the two factors. -/
def swapHom : squareObj k ⟶ squareObj k :=
  ObjectProperty.homMk (specOverHom k (swap k).toAlgHom)

/-- The automorphism of `k[u₁, u₂, v₁, v₂]` exchanging the two factors is an involution. -/
theorem swap_comp_swap : (swap k).toAlgHom.comp (swap k).toAlgHom = AlgHom.id k (ring k) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  fin_cases j <;> simp [swap]

/-- Exchanging the two factors carries the `j`-th factor map to the other one. -/
theorem swap_comp_factorMap (j : Fin 2) :
    (swap k).toAlgHom.comp (factorMap k j) = factorMap k (Equiv.swap 0 1 j) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [factorMap, swap]

/-- Composing the involution `σ` with the `j`-th projection gives the other projection. -/
theorem swapHom_comp_proj (j : Fin 2) :
    swapHom k ≫ proj k j = proj k (Equiv.swap 0 1 j) := by
  ext : 1
  change specOverHom k (swap k).toAlgHom ≫ specOverHom k (factorMap k j) = _
  rw [specOverHom_comp, swap_comp_factorMap]
  rfl

/-! ### The cycle `α` -/

/-- The value at an object `T` of the functor `S' ↦ z^eff(X'/S', 0)` for the plane. -/
abbrev Cyc (T : LocallyOfFiniteTypeOver (Spec (.of k))) : Type u :=
  ↥(effectiveRelativeCycles (pullback.snd (planeHom k) T.obj.hom) 0)

/-- The pullback along `e : T ⟶ X` of the diagonal cycle of `X/S`: the cycle of the graph of
`e`. -/
abbrev graphCycle {T : LocallyOfFiniteTypeOver (Spec (.of k))} (e : T ⟶ planeObj k) : Cyc k T :=
  effectiveRelativeCyclesMap (planeHom k) 0 e (diagonalRelativeCycle (planeHom k))

/-- The pullback along `g : T' ⟶ T` of the graph cycle of `e` is the graph cycle of `g ≫ e`. -/
theorem effectiveRelativeCyclesMap_graphCycle {T T' : LocallyOfFiniteTypeOver (Spec (.of k))}
    (g : T' ⟶ T) (e : T ⟶ planeObj k) :
    effectiveRelativeCyclesMap (planeHom k) 0 g (graphCycle k e) = graphCycle k (g ≫ e) := by
  rw [graphCycle, graphCycle, effectiveRelativeCyclesMap_comp]
  rfl

/-- **The canonical relative `0`-cycle `α ∈ z^eff(X_W/W, 0)`**: over `w = (x₁, x₂) ∈ W = X ×_S X`
it is `[x₁] + [x₂]`, the sum of the pullbacks of the diagonal cycle of `X/S` along the two
projections, that is the sum of the cycles of the graphs of the two projections. -/
def alpha : Cyc k (squareObj k) := graphCycle k (proj k 0) + graphCycle k (proj k 1)

/-- **`α` is invariant under the involution exchanging the two factors.** -/
theorem map_swapHom_alpha :
    effectiveRelativeCyclesMap (planeHom k) 0 (swapHom k) (alpha k) = alpha k := by
  rw [alpha, effectiveRelativeCyclesMap_add, effectiveRelativeCyclesMap_graphCycle,
    effectiveRelativeCyclesMap_graphCycle, swapHom_comp_proj, swapHom_comp_proj, add_comm]
  rfl

/-! ### The symmetric square and the basic opens -/

/-- The coordinate ring of `Sym²(X)` is finitely generated. -/
instance finiteType_sym : Algebra.FiniteType k (sym k) := by
  classical
  rw [← Subalgebra.fg_iff_finiteType]
  simpa [sym] using Subalgebra.fg_adjoin_finset (R := k)
    ({u₁ k + u₂ k, u₁ k * u₂ k, v₁ k + v₂ k, v₁ k * v₂ k, u₁ k * v₁ k + u₂ k * v₂ k} :
      Finset (ring k))

/-- The localization `R_h` of `k[u₁, u₂, v₁, v₂]` at an element of the symmetric subalgebra. -/
abbrev ringAway (h : sym k) : Type u := Localization.Away (algebraMap (sym k) (ring k) h)

/-- The localization `B_h` of the symmetric subalgebra at one of its elements. -/
abbrev symAway (h : sym k) : Type u := Localization.Away h

/-- The localization `R_h` is a finitely generated `k`-algebra. -/
instance (h : sym k) : Algebra.FiniteType k (ringAway k h) :=
  haveI : Algebra.FiniteType (ring k) (ringAway k h) :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (algebraMap (sym k) (ring k) h))
      (ringAway k h)
  Algebra.FiniteType.trans (S := ring k) inferInstance inferInstance

/-- The localization `B_h` is a finitely generated `k`-algebra. -/
instance (h : sym k) : Algebra.FiniteType k (symAway k h) :=
  haveI : Algebra.FiniteType (sym k) (symAway k h) :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers h) (symAway k h)
  Algebra.FiniteType.trans (S := sym k) inferInstance inferInstance

/-- The spectrum of the symmetric subalgebra is locally of finite type over `Spec k`. -/
instance : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (sym k)))) :=
  locallyOfFiniteType_specMap_algebraMap _ _

/-- `Spec R_h` is locally of finite type over `Spec k`. -/
instance (h : sym k) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (ringAway k h)))) :=
  locallyOfFiniteType_specMap_algebraMap _ _

/-- `Spec B_h` is locally of finite type over `Spec k`. -/
instance (h : sym k) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (symAway k h)))) :=
  locallyOfFiniteType_specMap_algebraMap _ _

/-- `Sym²(X) = Spec k[u₁ + u₂, u₁u₂, v₁ + v₂, v₁v₂, u₁v₁ + u₂v₂]`. -/
abbrev symObj : LocallyOfFiniteTypeOver (Spec (.of k)) :=
  objOf (Spec.map (CommRingCat.ofHom (algebraMap k (sym k))))

/-- The basic open `D(h) = Spec R_h` of `W`. -/
abbrev squareAwayObj (h : sym k) : LocallyOfFiniteTypeOver (Spec (.of k)) :=
  objOf (Spec.map (CommRingCat.ofHom (algebraMap k (ringAway k h))))

/-- The basic open `D(h) = Spec B_h` of `Sym²(X)`. -/
abbrev symAwayObj (h : sym k) : LocallyOfFiniteTypeOver (Spec (.of k)) :=
  objOf (Spec.map (CommRingCat.ofHom (algebraMap k (symAway k h))))

/-- The quotient morphism `q : W ⟶ Sym²(X)`. -/
def quot : squareObj k ⟶ symObj k :=
  ObjectProperty.homMk (specOverHom k (Subalgebra.val (sym k)))

/-- The map `B_h ⟶ R_h`, as a map of `k`-algebras. -/
def awayAlgHom (h : sym k) : symAway k h →ₐ[k] ringAway k h where
  __ := Localization.awayMap (algebraMap (sym k) (ring k)) h
  commutes' c := by
    change Localization.awayMap (algebraMap (sym k) (ring k)) h
      (algebraMap (sym k) (symAway k h) (algebraMap k (sym k) c)) = _
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    rfl

/-- The restriction `q_h : D(h) ⟶ D(h)` of the quotient morphism. -/
def quotAway (h : sym k) : squareAwayObj k h ⟶ symAwayObj k h :=
  ObjectProperty.homMk (specOverHom k (awayAlgHom k h))

/-- The inclusion `D(h) ⟶ W`. -/
def squareAwayι (h : sym k) : squareAwayObj k h ⟶ squareObj k :=
  ObjectProperty.homMk (specOverHom k (IsScalarTower.toAlgHom k (ring k) (ringAway k h)))

/-! ### The generic point of the diagonal and its image in `Sym²(X)` -/

/-- The point `(u, v)` of the plane with values in its function field `L = k(u, v)`. -/
abbrev coordPoint : MvPolynomial (Fin 2) k →ₐ[k] funField k :=
  IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k) (funField k)

/-- Each factor of the generic point of the diagonal is the point `(u, v)` of the plane. -/
theorem diagonalPoint_comp_factorMap (j : Fin 2) :
    (diagonalPoint k).comp (factorMap k j) = coordPoint k := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [diagonalPoint, factorMap]

/-- `Spec L`, `L = k(u, v)`, over `Spec k`. -/
abbrev funFieldOver : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (funField k))))

/-- `Spec K₀`, `K₀ = k(u², v²)`, over `Spec k`. -/
abbrev squareFieldOver : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (squareField k))))

/-- The generic point of the diagonal, `Spec L ⟶ W`. -/
abbrev diagPt : funFieldOver k ⟶ (squareObj k).obj := specOverHom k (diagonalPoint k)

/-- `Spec L ⟶ Spec K₀`. -/
abbrev fieldExt : funFieldOver k ⟶ squareFieldOver k := specOverHom k (squareField k).val

/-- The point `(u, v)` of the plane, `Spec L ⟶ X`. -/
abbrev coordPt : funFieldOver k ⟶ (planeObj k).obj := specOverHom k (coordPoint k)

/-- Both projections of the generic point of the diagonal are the point `(u, v)` of `X`. -/
theorem diagPt_comp_proj (j : Fin 2) : diagPt k ≫ (proj k j).hom = coordPt k := by
  change specOverHom k (diagonalPoint k) ≫ specOverHom k (factorMap k j) = _
  rw [specOverHom_comp, diagonalPoint_comp_factorMap]

/-- The section of `X ×_S Spec L ⟶ Spec L` given by the point `(u, v)`. -/
abbrev coordSection : Spec (.of (funField k)) ⟶ pullback (planeHom k) (funFieldOver k).hom :=
  graphSection (planeHom k) (coordPt k)

variable [CharP k 2]

/-- A morphism `Φ` into a fibre product hits, on residue fields, everything the residue field maps
of its two components hit. -/
theorem exists_residueFieldMap_eq_of_comp_eq {X Y Z : Scheme.{u}} (g : X ⟶ Y) (p : Y ⟶ Z)
    (m : X ⟶ Z) (hm : g ≫ p = m) (x : X) (w : X.residueField x)
    (hw : ∃ z, m.residueFieldMap x z = w) : ∃ z, g.residueFieldMap x z = w := by
  subst hm
  obtain ⟨z, rfl⟩ := hw
  exact exists_residueFieldMap_eq_of_comp g p x z

omit [CharP k 2] in
/-- **The residue field of the point `(u, v)` of `X ×_S Spec K₀` is `L`.** The point of
`X ×_S Spec K₀` below the point `(u, v)` of `X ×_S Spec L` has residue field generated by `K₀`
and the coordinates `u, v`, that is all of `L`. -/
theorem surjective_residueFieldMap_coordSection (t : Spec (.of (funField k))) :
    Function.Surjective
      ((coordSection k ≫ overBaseChangeMap (planeHom k) (fieldExt k)).residueFieldMap t) := by
  set g := coordSection k ≫ overBaseChangeMap (planeHom k) (fieldExt k)
  have hfst : g ≫ pullback.fst (planeHom k) (squareFieldOver k).hom = (coordPt k).left := by
    simp only [g, overBaseChangeMap, Category.assoc, pullback.lift_fst]
  have hsnd : g ≫ pullback.snd (planeHom k) (squareFieldOver k).hom = (fieldExt k).left := by
    simp only [g, overBaseChangeMap, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc]
    exact Category.id_comp _
  set iL := specFieldResidueEquiv (funField k) t
  set F := (g.residueFieldMap t).hom.fieldRange
  have hmem : ∀ (C : Type u) [CommRing C] (φ : C →+* funField k)
      (p : pullback (planeHom k) (squareFieldOver k).hom ⟶ Spec (.of C))
      (_ : g ≫ p = Spec.map (CommRingCat.ofHom φ)) (c : C), iL (φ c) ∈ F :=
    fun C _ φ p hp c => exists_residueFieldMap_eq_of_comp_eq g p _ hp t _
      (exists_residueFieldMap_specMap_eq φ t c)
  have hK₀ : ∀ c : squareField k, iL (c : funField k) ∈ F := fun c =>
    hmem _ (squareField k).val.toRingHom _ hsnd c
  have hu : iL (fu k) ∈ F := hmem _ (coordPoint k).toRingHom _ hfst (X 0)
  have hv : iL (fv k) ∈ F := hmem _ (coordPoint k).toRingHom _ hfst (X 1)
  let T : IntermediateField (squareField k) (funField k) :=
    (F.comap iL.toRingHom).toIntermediateField fun c => hK₀ c
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← adjoin_squareField_eq_top, IntermediateField.adjoin_le_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl <;> assumption
  intro w
  obtain ⟨z, hz⟩ : iL.symm w ∈ T := hT ▸ IntermediateField.mem_top
  exact ⟨z, hz.trans (iL.apply_symm_apply w)⟩

/-- **No base change from `Spec K₀` is `2 [(u, v)]`.** For every scheme `O` over `S` with a
point `ε : Spec K₀ ⟶ O` and every family `γ` of `0`-cycles on `X ×_S O / O`, the base change of `γ`
along `Spec L ⟶ Spec K₀ ⟶ O` is not the cycle `2 [(u, v)]` on `A²_L`: base change along the
purely inseparable extension `L/K₀`, of degree at least `3`, multiplies the coefficient of a
rational point by `[L : K₀]`. -/
theorem not_forall_baseChange_eq_two (O : Over (Spec (.of k)))
    (γ : FamilyOfCycles (pullback.snd (planeHom k) O.hom) 0) (ε : squareFieldOver k ⟶ O)
    (t : Spec (.of (funField k))) (Q : (pullback.snd (planeHom k) (funFieldOver k).hom).fiber t)
    (hQ : (pullback.snd (planeHom k) (funFieldOver k).hom).fiberι t Q = coordSection k t) :
    ¬ ∀ x, (baseChangeFamilyOfIsPullback (pullback.snd (planeHom k) O.hom)
      (isPullback_overBaseChange (planeHom k) (fieldExt k ≫ ε)) 0 γ t : AlgebraicCycle _ ℤ) x =
        open Classical in if x = Q then 2 else 0 := by
  classical
  intro hall
  rw [← baseChangeFamilyOfIsPullback_overBaseChange_comp] at hall
  have hfr : let := ((fieldExt k).left.residueFieldMap t).hom.toAlgebra
      Module.finrank ((squareFieldOver k).left.residueField ((fieldExt k).left t))
        ((funFieldOver k).left.residueField t) =
        Module.finrank (squareField k) (funField k) :=
    finrank_residueFieldMap_specMap (squareField k) (funField k) t
  have h3 := three_le_finrank_squareField k
  have hd := finrank_dvd_of_baseChangeFamilyOfIsPullback_eq_single
    (pullback.snd (planeHom k) (squareFieldOver k).hom)
    (isPullback_overBaseChange (planeHom k) (fieldExt k)) t _ Q 2
    (hfin := by
      let := ((fieldExt k).left.residueFieldMap t).hom.toAlgebra
      exact Module.finite_of_finrank_pos (by rw [hfr]; omega))
    (residueDegree_restrictedFiberMap_eq_one_of_section _ _ _ _ _ t (coordSection k)
      (surjective_residueFieldMap_coordSection k t) Q hQ) (by convert hall)
  rw [hfr] at hd
  have := Int.le_of_dvd (by norm_num) hd
  omega

omit [CharP k 2] in
/-- **The base change of `α` to the generic point of the diagonal is `2 [(u, v)]`**: both points
`x₁` and `x₂` of the cycle `α_w = [x₁] + [x₂]` become the point `(u, v)` there. -/
theorem baseChange_alpha_apply (t : Spec (.of (funField k)))
    (x : (pullback.snd (planeHom k) (funFieldOver k).hom).fiber t) :
    (baseChangeFamilyOfIsPullback (pullback.snd (planeHom k) (squareObj k).obj.hom)
      (isPullback_overBaseChange (planeHom k) (diagPt k)) 0 (alpha k).1.1 t :
        AlgebraicCycle _ ℤ) x =
      open Classical in
      if (pullback.snd (planeHom k) (funFieldOver k).hom).fiberι t x = coordSection k t
      then 2 else 0 := by
  classical
  have hj : ∀ j, baseChangeFamilyOfIsPullback (pullback.snd (planeHom k) (squareObj k).obj.hom)
      (isPullback_overBaseChange (planeHom k) (diagPt k)) 0 (graphCycle k (proj k j)).1.1 =
      familyAssociatedToClosedSubscheme (pullback.snd (planeHom k) (funFieldOver k).hom)
        (coordSection k) 0 := by
    intro j
    change baseChangeFamilyOfIsPullback _ _ 0 (baseChangeFamilyOfIsPullback
      (pullback.snd (planeHom k) (Over.mk (planeHom k)).hom)
      (isPullback_overBaseChange (planeHom k) (proj k j).hom) 0
      (familyAssociatedToClosedSubscheme (pullback.snd (planeHom k) (Over.mk (planeHom k)).hom)
        (graphSection (planeHom k) (𝟙 _)) 0)) = _
    rw [baseChangeFamilyOfIsPullback_overBaseChange_comp, diagPt_comp_proj,
      baseChangeFamilyOfIsPullback_diagonal]
  have hval := familyAssociatedToClosedSubscheme_apply_of_section
    (pullback.snd (planeHom k) (funFieldOver k).hom) (coordSection k)
    (graphSection_snd (planeHom k) (coordPt k)) t x
  rw [show (alpha k).1.1 = (graphCycle k (proj k 0)).1.1 + (graphCycle k (proj k 1)).1.1 from rfl,
    baseChangeFamilyOfIsPullback_add, hj, hj, Pi.add_apply, AddSubgroup.coe_add,
    Function.locallyFinsuppWithin.coe_add, Pi.add_apply, hval]
  split_ifs <;> norm_num

/-! ### There is no cycle `β` on `Sym²(X)` pulling back to `α` -/

/-- The coordinate ring of `Sym²(X)` maps into `K₀ = k(u², v²)` under the generic point of the
diagonal. -/
def symToSquareField : sym k →ₐ[k] squareField k :=
  ((diagonalPoint k).comp (sym k).val).codRestrict (squareField k).toSubalgebra
    fun x => diagonalPoint_mem_squareField k x.2

/-- The generic point `η` of the image of the diagonal, `Spec K₀ ⟶ Sym²(X)`. -/
abbrev symPt : squareFieldOver k ⟶ (symObj k).obj := specOverHom k (symToSquareField k)

/-- The square formed by `Spec L ⟶ Spec K₀`, `η`, the generic point of the diagonal and the
quotient morphism `q` commutes. -/
theorem fieldExt_comp_symPt : fieldExt k ≫ symPt k = diagPt k ≫ (quot k).hom := by
  change specOverHom k _ ≫ specOverHom k _ = specOverHom k _ ≫ specOverHom k _
  rw [specOverHom_comp, specOverHom_comp]
  congr 1

omit [CharP k 2] in
/-- The point of the fibre of `X ×_S Spec L ⟶ Spec L` on the section `(u, v)`. -/
theorem exists_fiber_coordSection (t : Spec (.of (funField k))) :
    ∃ Q, (pullback.snd (planeHom k) (funFieldOver k).hom).fiberι t Q = coordSection k t := by
  change coordSection k t ∈ Set.range ((pullback.snd (planeHom k) (funFieldOver k).hom).fiberι t)
  rw [Scheme.Hom.range_fiberι]
  change (coordSection k ≫ pullback.snd _ _) t = t
  rw [graphSection_snd]
  rfl

/-- There is no `γ` on `O` whose base change along `Spec L ⟶ Spec K₀ ⟶ O` is the base change of
`α` to the generic point of the diagonal. -/
private theorem false_of_baseChange_fieldExt_eq_alpha (O : Over (Spec (.of k)))
    (γ : FamilyOfCycles (pullback.snd (planeHom k) O.hom) 0) (ε : squareFieldOver k ⟶ O)
    (h : baseChangeFamilyOfIsPullback (pullback.snd (planeHom k) O.hom)
        (isPullback_overBaseChange (planeHom k) (fieldExt k ≫ ε)) 0 γ =
      baseChangeFamilyOfIsPullback (pullback.snd (planeHom k) (squareObj k).obj.hom)
        (isPullback_overBaseChange (planeHom k) (diagPt k)) 0 (alpha k).1.1) : False := by
  classical
  let t : Spec (.of (funField k)) := Nonempty.some inferInstance
  obtain ⟨Q, hQ⟩ := exists_fiber_coordSection k t
  refine not_forall_baseChange_eq_two k O γ ε t Q hQ fun x => ?_
  rw [h, baseChange_alpha_apply]
  congr 1
  exact propext ((Scheme.Hom.fiberι _ t).isEmbedding.injective.eq_iff' hQ)

/-- **Stacks Project, Remark 0H5Y, the characteristic `2` example: there is no cycle `β`.** Let
`k` be a field of characteristic `2`, `X = A²_k`, `W = X ×_k X` and `Sym²(X) = Spec B` with
`B = k[u₁ + u₂, u₁u₂, v₁ + v₂, v₁v₂, u₁v₁ + u₂v₂]`. No family `β` of `0`-cycles on the fibres of
`X ×_k Sym²(X) ⟶ Sym²(X)`, in particular no relative `0`-cycle, pulls back along the quotient
morphism `W ⟶ Sym²(X)` to the cycle `α` with `α_{(x₁, x₂)} = [x₁] + [x₂]`: at the generic point
`η` of the image `V = Spec k[u₁², v₁²]` of the diagonal the cycle `β_η` would be a `0`-cycle on
`A²_{k(u₁², v₁²)}` whose pullback to `A²_{k(u₁, v₁)}` is twice the rational point `(u₁, v₁)`, which
is impossible. -/
@[stacks 0H5Y "in characteristic 2 the cycle α on A² × A² does not descend to Sym²(A²): there is \
no cycle β whose pullback to W is α"]
theorem baseChange_quot_ne_alpha
    (β : FamilyOfCycles (pullback.snd (planeHom k) (symObj k).obj.hom) 0) :
    baseChangeFamilyOfIsPullback (pullback.snd (planeHom k) (symObj k).obj.hom)
      (isPullback_overBaseChange (planeHom k) (quot k).hom) 0 β ≠ (alpha k).1.1 := by
  intro heq
  exact false_of_baseChange_fieldExt_eq_alpha k _ β (symPt k) (by
    rw [fieldExt_comp_symPt, ← baseChangeFamilyOfIsPullback_overBaseChange_comp, heq])

/-- The form of `Stacks.Chow.SymPlane.baseChange_quot_ne_alpha` for the functor: no
`β ∈ z^eff(X ×_k Sym²(X) / Sym²(X), 0)` maps to `α` under `q : W ⟶ Sym²(X)`. -/
theorem map_quot_ne_alpha (β : Cyc k (symObj k)) :
    effectiveRelativeCyclesMap (planeHom k) 0 (quot k) β ≠ alpha k := fun heq =>
  baseChange_quot_ne_alpha k β.1.1 (congrArg (fun γ : Cyc k (squareObj k) => γ.1.1) heq)

/-! ### The same over a basic open around the generic point of the image of the diagonal -/

/-- A monoid map sends every power of an element with unit image to a unit. -/
private theorem isUnit_map_of_mem_powers {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {h : M}
    (hh : IsUnit (f h)) (y : Submonoid.powers h) : IsUnit (f y) :=
  Submonoid.powers_le.mpr (show h ∈ (IsUnit.submonoid N).comap f from hh) y.2

variable {k} in
omit [CharP k 2] in
/-- If `h` does not vanish at the generic point of the diagonal, then every power of its image
in `k[u₁, u₂, v₁, v₂]` maps to a unit of `L`. -/
theorem isUnit_diagonalPoint_pow {h : sym k} (hh : diagonalPoint k h ≠ 0)
    (y : Submonoid.powers (algebraMap (sym k) (ring k) h)) : IsUnit (diagonalPoint k y) := by
  exact isUnit_map_of_mem_powers (diagonalPoint k : ring k →* funField k)
    (isUnit_iff_ne_zero.mpr hh) y

variable {k} in
/-- If `h` does not vanish at the generic point of the diagonal, then every power of `h` maps to
a unit of `K₀`. -/
theorem isUnit_symToSquareField_pow {h : sym k} (hh : diagonalPoint k h ≠ 0)
    (y : Submonoid.powers h) : IsUnit (symToSquareField k y) := by
  exact isUnit_map_of_mem_powers (symToSquareField k : sym k →* squareField k)
    (isUnit_iff_ne_zero.mpr fun h0 => hh (congrArg Subtype.val h0)) y

/-- The generic point of the diagonal, `Spec L ⟶ D(h) ⊆ W`. -/
abbrev diagPtAway (h : sym k) (hh : diagonalPoint k h ≠ 0) :
    funFieldOver k ⟶ (squareAwayObj k h).obj :=
  specOverHom k (IsLocalization.liftAlgHom (M := Submonoid.powers (algebraMap (sym k) (ring k) h))
    (S := ringAway k h) (f := diagonalPoint k) (isUnit_diagonalPoint_pow hh))

/-- The generic point of the image of the diagonal, `Spec K₀ ⟶ D(h) ⊆ Sym²(X)`. -/
abbrev symPtAway (h : sym k) (hh : diagonalPoint k h ≠ 0) :
    squareFieldOver k ⟶ (symAwayObj k h).obj :=
  specOverHom k (IsLocalization.liftAlgHom (M := Submonoid.powers h) (S := symAway k h)
    (f := symToSquareField k) (isUnit_symToSquareField_pow hh))

omit [CharP k 2] in
/-- The generic point of the diagonal in `D(h)`, followed by the inclusion `D(h) ⟶ W`, is the
generic point of the diagonal in `W`. -/
theorem diagPtAway_comp_ι (h : sym k) (hh : diagonalPoint k h ≠ 0) :
    diagPtAway k h hh ≫ (squareAwayι k h).hom = diagPt k := by
  change specOverHom k _ ≫ specOverHom k _ = _
  rw [specOverHom_comp]
  congr 1
  ext r
  change IsLocalization.lift _ (algebraMap (ring k) (ringAway k h) (MvPolynomial.X r)) = _
  rw [IsLocalization.lift_eq]
  rfl

/-- The square formed by `Spec L ⟶ Spec K₀`, the generic points over `D(h)` and the restricted
quotient morphism `q_h` commutes. -/
theorem fieldExt_comp_symPtAway (h : sym k) (hh : diagonalPoint k h ≠ 0) :
    fieldExt k ≫ symPtAway k h hh = diagPtAway k h hh ≫ (quotAway k h).hom := by
  change specOverHom k _ ≫ specOverHom k _ = specOverHom k _ ≫ specOverHom k _
  rw [specOverHom_comp, specOverHom_comp]
  congr 1
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers h)
  ext b
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, AlgHom.coe_comp]
  change ((IsLocalization.liftAlgHom _ (algebraMap (sym k) (symAway k h) b) : squareField k) :
    funField k) = IsLocalization.liftAlgHom _ (Localization.awayMap (algebraMap (sym k) (ring k)) h
      (algebraMap (sym k) (symAway k h) b))
  rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq,
    IsLocalization.coe_liftAlgHom, IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq,
    IsLocalization.lift_eq]
  rfl

/-- **No cycle over a basic open of `Sym²(X)` around `η` pulls back to `α`.** For `h ∈ B` not
vanishing at the generic point of the image of the diagonal, no `β ∈ z^eff(X_{D(h)}/D(h), 0)`
pulls back along `q_h : D(h) ⟶ D(h)` to the restriction of `α`. -/
theorem map_quotAway_ne (h : sym k) (hh : diagonalPoint k h ≠ 0) (β : Cyc k (symAwayObj k h)) :
    effectiveRelativeCyclesMap (planeHom k) 0 (quotAway k h) β ≠
      effectiveRelativeCyclesMap (planeHom k) 0 (squareAwayι k h) (alpha k) := by
  intro heq
  have h1 := congrArg (fun γ : Cyc k (squareAwayObj k h) => γ.1.1) heq
  simp only [effectiveRelativeCyclesMap_coe] at h1
  exact false_of_baseChange_fieldExt_eq_alpha k _ β.1.1 (symPtAway k h hh) (by
    rw [fieldExt_comp_symPtAway, ← baseChangeFamilyOfIsPullback_overBaseChange_comp, h1,
      baseChangeFamilyOfIsPullback_overBaseChange_comp, diagPtAway_comp_ι])

/-! ### Non-representability -/

omit [CharP k 2] in
/-- A morphism `Spec D ⟶ Spec k` is determined by its composite with `Spec C ⟶ Spec D` for an
injective ring map `D → C`. -/
theorem specMap_comp_cancel {C D : Type u} [CommRing C] [CommRing D] (ι : D →+* C)
    (hι : Function.Injective ι) {g₁ g₂ : Spec (.of D) ⟶ Spec (.of k)}
    (h : Spec.map (CommRingCat.ofHom ι) ≫ g₁ = Spec.map (CommRingCat.ofHom ι) ≫ g₂) : g₁ = g₂ := by
  obtain ⟨ζ₁, rfl⟩ := Spec.map_surjective g₁
  obtain ⟨ζ₂, rfl⟩ := Spec.map_surjective g₂
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  congr 1
  ext c
  exact hι (congrArg (fun m : CommRingCat.of k ⟶ CommRingCat.of C => m c) (Spec.map_injective h))

omit [CharP k 2] in
/-- The involution `σ` of `k[u₁, u₂, v₁, v₂]` squares to the identity. -/
theorem swap_swap_apply (r : ring k) : swap k (swap k r) = r := by
  simpa using congrArg (fun φ : ring k →ₐ[k] ring k => φ r) (swap_comp_swap k)

omit [CharP k 2] in
/-- The involution `σ` fixes the generic point of the diagonal. -/
theorem swap_mem_asIdeal_diagPt_iff (t : Spec (.of (funField k))) (r : ring k) :
    swap k r ∈ ((diagPt k).left t).asIdeal ↔ r ∈ ((diagPt k).left t).asIdeal := by
  change diagonalPoint k (swap k r) ∈ (t.asIdeal : Ideal (funField k)) ↔
    diagonalPoint k r ∈ (t.asIdeal : Ideal (funField k))
  rw [show diagonalPoint k (swap k r) = diagonalPoint k r from
    congrArg (fun φ : ring k →ₐ[k] funField k => φ r) (diagonalPoint_comp_swap k)]

omit [CharP k 2] in
/-- The localization `B_h → R_h` of the inclusion `B ⊆ k[u₁, u₂, v₁, v₂]` is injective. -/
theorem injective_awayMap_sym (h : sym k) :
    Function.Injective (Localization.awayMap (algebraMap (sym k) (ring k)) h) := by
  rw [Localization.awayMap_injective_iff]
  intro a ha
  refine ⟨0, ?_⟩
  rw [pow_zero, one_mul]
  exact Subtype.ext ha

/-- **Stacks Project, Remark 0H5Y, the characteristic `2` example.** Let `k` be a field of
characteristic `2` and `X = A²_k`. On any full subcategory of the schemes of finite type over
`k` containing `W = X ×_k X` and the principal open subschemes of `W` and of
`Sym²(X) = W/⟨σ⟩`, the functor `S' ↦ z^eff(S' ×_k X / S', 0)` is not representable. Such is the
category of weakly normal schemes of finite type over `k`
(`Stacks.Chow.SymPlane.not_isRepresentable_weaklyNormal`), so replacing seminormality by weak
normality does not make the functor representable when the base has points of positive
characteristic.

If `M` represented the functor, the cycle `α` would be a morphism `W ⟶ M` invariant under the
involution `σ` exchanging the factors, because `α` is; near the generic point of the image of the
diagonal it would factor through `W ⟶ Sym²(X)`, and the cycle `β` on `Sym²(X)` corresponding to
the factorization would pull back to `α`. There is no such cycle
(`Stacks.Chow.SymPlane.map_quotAway_ne`). -/
@[stacks 0H5Y "in characteristic 2 the functor is not representable on any category of schemes \
of finite type over k containing W and the principal opens of W and of Sym²(X)"]
theorem not_isRepresentable_of_le (P : ObjectProperty (LocallyOfFiniteTypeOver (Spec (.of k))))
    (hW : P (squareObj k))
    (hP : ∀ h : sym k, h ≠ 0 → P (squareAwayObj k h) ∧ P (symAwayObj k h)) :
    ¬ (P.ι.op ⋙ effectiveRelativeCyclesFunctor (planeHom k) 0).IsRepresentable := by
  classical
  rintro ⟨M, ⟨Rep⟩⟩
  let Wp : P.FullSubcategory := ⟨squareObj k, hW⟩
  let φ : Wp ⟶ M := Rep.homEquiv.symm (alpha k)
  have hφα : Rep.homEquiv φ = alpha k := Equiv.apply_symm_apply _ _
  -- `φ` is invariant under the involution
  have hσ : (ObjectProperty.homMk (swapHom k) : Wp ⟶ Wp) ≫ φ = φ := Rep.homEquiv.injective <| by
    rw [Rep.homEquiv_comp, hφα]
    exact map_swapHom_alpha k
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Spec (.of (ring k)) ⟶ M.obj.obj.left, Φ = φ.hom.hom.left := ⟨_, rfl⟩
  have hΦ : Spec.map (CommRingCat.ofHom (swap k).toAlgHom.toRingHom) ≫ Φ = Φ := by
    rw [hΦdef]
    exact congrArg (fun m : Wp ⟶ M => m.hom.hom.left) hσ
  -- the generic point of the diagonal is fixed
  let t : Spec (.of (funField k)) := Nonempty.some inferInstance
  obtain ⟨h, hhx, ψ₀, hψ₀⟩ := exists_factor_specAway_of_comp_eq (sym k) (swap k)
    (swap_swap_apply k) (mem_sym_iff (k := k)) Φ hΦ ((diagPt k).left t)
    (swap_mem_asIdeal_diagPt_iff k t)
  have hh : diagonalPoint k h ≠ 0 := fun h0 => hhx <| by
    change diagonalPoint k (h : ring k) ∈ (t.asIdeal : Ideal (funField k))
    rw [h0]
    exact zero_mem _
  -- `ψ₀` lies over `Spec k`
  have hw : ψ₀ ≫ M.obj.obj.hom = (symAwayObj k h).obj.hom := by
    refine specMap_comp_cancel k _ (injective_awayMap_sym k h) ?_
    rw [← Category.assoc, hψ₀, Category.assoc, hΦdef, Over.w φ.hom.hom]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext c
    exact ((awayAlgHom k h).commutes c).symm
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hh (map_zero _)
  let Sp : P.FullSubcategory := ⟨symAwayObj k h, (hP h hh0).2⟩
  let Wh : P.FullSubcategory := ⟨squareAwayObj k h, (hP h hh0).1⟩
  let ψ : Sp ⟶ M := ObjectProperty.homMk (ObjectProperty.homMk (Over.homMk ψ₀ hw))
  let qh : Wh ⟶ Sp := ObjectProperty.homMk (quotAway k h)
  let ιh : Wh ⟶ Wp := ObjectProperty.homMk (squareAwayι k h)
  have hfac : qh ≫ ψ = ιh ≫ φ := by
    ext : 3
    change Spec.map _ ≫ ψ₀ = Spec.map _ ≫ φ.hom.hom.left
    rw [← hΦdef]
    exact hψ₀
  refine map_quotAway_ne k h hh (Rep.homEquiv ψ) ?_
  have h1 := congrArg Rep.homEquiv hfac
  rwa [Rep.homEquiv_comp, Rep.homEquiv_comp, hφα] at h1

/-- A representable functor on the category of schemes locally of finite type over `S` stays
representable on the full subcategory of all of them. -/
theorem isRepresentable_top_ι {S : Scheme.{u}}
    (F : (LocallyOfFiniteTypeOver S)ᵒᵖ ⥤ Type u) [F.IsRepresentable] :
    ((⊤ : ObjectProperty (LocallyOfFiniteTypeOver S)).ι.op ⋙ F).IsRepresentable := by
  obtain ⟨M, ⟨R⟩⟩ := (inferInstance : F.IsRepresentable)
  exact ⟨⟨M, trivial⟩, ⟨{
    homEquiv := fun {X} => (ObjectProperty.fullyFaithfulι _).homEquiv.trans R.homEquiv
    homEquiv_comp := fun f g => R.homEquiv_comp f.hom g.hom }⟩⟩

/-- **Stacks Project, Remark 0H5Y, the characteristic `2` example, on all schemes of finite type.**
For `k` of characteristic `2` and `X = A²_k`, the functor `S' ↦ z^eff(S' ×_k X / S', 0)` on
schemes locally of finite type over `k` is not representable. -/
theorem not_isRepresentable :
    ¬ (effectiveRelativeCyclesFunctor (planeHom k) 0).IsRepresentable := fun _h =>
  not_isRepresentable_of_le k ⊤ trivial (fun _ _ => ⟨trivial, trivial⟩) (isRepresentable_top_ι _)

/-- The restriction `k[u₁, u₂, v₁, v₂] → k[u, v]` to the diagonal, `uᵢ ↦ u`, `vᵢ ↦ v`. -/
def diagonalRestriction : ring k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval fun ij => X ij.1

/-- **The image of the diagonal in `Sym²(X)` is `V = Spec k[u², v²]`**, in characteristic `2`:
the coordinate ring of `Sym²(X)` restricts on the diagonal to `k[u², v²]`. -/
@[stacks 0H5Y "the image of the diagonal in Sym²(X) is V = Spec k[u₁², v₁²]"]
theorem map_sym_diagonalRestriction :
    (sym k).map (diagonalRestriction k) =
      Algebra.adjoin k {(X 0 : MvPolynomial (Fin 2) k) ^ 2, X 1 ^ 2} := by
  have h2 : (2 : MvPolynomial (Fin 2) k) = 0 := by
    have h := congrArg (algebraMap k (MvPolynomial (Fin 2) k)) (CharTwo.two_eq_zero (R := k))
    rwa [map_ofNat, map_zero] at h
  rw [sym, AlgHom.map_adjoin]
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · have : diagonalRestriction k (u₁ k + u₂ k) = 0 := by
        simp [diagonalRestriction]
        linear_combination (X 0 : MvPolynomial (Fin 2) k) * h2
      rw [this]
      exact zero_mem _
    · have : diagonalRestriction k (u₁ k * u₂ k) = X 0 ^ 2 := by simp [diagonalRestriction, sq]
      rw [this]
      exact Algebra.subset_adjoin (by simp)
    · have : diagonalRestriction k (v₁ k + v₂ k) = 0 := by
        simp [diagonalRestriction]
        linear_combination (X 1 : MvPolynomial (Fin 2) k) * h2
      rw [this]
      exact zero_mem _
    · have : diagonalRestriction k (v₁ k * v₂ k) = X 1 ^ 2 := by simp [diagonalRestriction, sq]
      rw [this]
      exact Algebra.subset_adjoin (by simp)
    · have : diagonalRestriction k (u₁ k * v₁ k + u₂ k * v₂ k) = 0 := by
        simp [diagonalRestriction]
        linear_combination (X 0 * X 1 : MvPolynomial (Fin 2) k) * h2
      rw [this]
      exact zero_mem _
  · rw [Algebra.adjoin_le_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Algebra.subset_adjoin ⟨u₁ k * u₂ k, by simp, by simp [diagonalRestriction, sq]⟩
    · exact Algebra.subset_adjoin ⟨v₁ k * v₂ k, by simp, by simp [diagonalRestriction, sq]⟩

/-! ### Weak normality -/

/-- `W = A² × A²` is normal: its coordinate ring is a polynomial ring, a unique factorization
domain. -/
instance isIntegrallyClosed_ring : IsIntegrallyClosed (ring k) := inferInstance

/-- **`Sym²(X)` is normal**: the ring of invariants of an involution of an integrally closed
domain is integrally closed. -/
instance isIntegrallyClosed_sym : IsIntegrallyClosed (sym k) := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing (sym k))]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := sym k) x
  have hinj : Function.Injective (algebraMap (sym k) (ring k)) := Subtype.val_injective
  let θ : FractionRing (sym k) →+* FractionRing (ring k) := IsFractionRing.map hinj
  have hθ : ∀ c : sym k, θ (algebraMap _ _ c) = algebraMap (ring k) _ (c : ring k) := fun c =>
    IsLocalization.map_eq _ c
  have hb0 : (b : ring k) ≠ 0 := fun h0 => nonZeroDivisors.ne_zero hb (Subtype.ext h0)
  -- the image of `x` is integral over `R`, hence in `R`
  have hint : _root_.IsIntegral (ring k) (θ (algebraMap _ _ a / algebraMap _ _ b)) := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map (algebraMap (sym k) (ring k)), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq]
    have : (algebraMap (ring k) (FractionRing (ring k))).comp (algebraMap (sym k) (ring k)) =
        θ.comp (algebraMap (sym k) (FractionRing (sym k))) := RingHom.ext fun c => (hθ c).symm
    rw [IsScalarTower.algebraMap_eq (sym k) (ring k) (FractionRing (ring k)), this,
      ← Polynomial.hom_eval₂, hpx, map_zero]
  obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ring k)
    (K := FractionRing (ring k))).mp hint
  have hbθ : algebraMap (ring k) (FractionRing (ring k)) (b : ring k) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
  have har : (a : ring k) = r * b := by
    apply IsFractionRing.injective (ring k) (FractionRing (ring k))
    rw [map_mul, hr, map_div₀, hθ, hθ, div_mul_cancel₀ _ hbθ]
  -- `r` is invariant
  have hσr : swap k r = r := by
    have h1 := congrArg (swap k) har
    rw [map_mul, swap_sym a.2, swap_sym b.2] at h1
    exact mul_right_cancel₀ hb0 (h1.symm.trans har)
  refine ⟨⟨r, (mem_sym_iff r).mpr hσr⟩, ?_⟩
  have hbB : algebraMap (sym k) (FractionRing (sym k)) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero hb)
  rw [eq_div_iff hbB, ← map_mul]
  congr 1
  exact Subtype.ext har.symm

omit [CharP k 2] in
/-- For `h ≠ 0`, the localization `R_h` is a domain. -/
theorem isDomain_ringAway {h : sym k} (hh : h ≠ 0) : IsDomain (ringAway k h) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := Submonoid.powers (algebraMap (sym k) (ring k) h)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors fun h0 => hh (Subtype.ext h0))

omit [CharP k 2] in
/-- For `h ≠ 0`, the localization `R_h` is integrally closed. -/
theorem isIntegrallyClosed_ringAway {h : sym k} (hh : h ≠ 0) :
    IsIntegrallyClosed (ringAway k h) :=
  isIntegrallyClosed_of_isLocalization _ (Submonoid.powers (algebraMap (sym k) (ring k) h))
    (powers_le_nonZeroDivisors_of_noZeroDivisors fun h0 => hh (Subtype.ext h0))

omit [CharP k 2] in
/-- For `h ≠ 0`, the localization `B_h` is a domain. -/
theorem isDomain_symAway {h : sym k} (hh : h ≠ 0) : IsDomain (symAway k h) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers h) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hh)

/-- For `h ≠ 0`, the localization `B_h` is integrally closed. -/
theorem isIntegrallyClosed_symAway {h : sym k} (hh : h ≠ 0) :
    IsIntegrallyClosed (symAway k h) :=
  isIntegrallyClosed_of_isLocalization (symAway k h) (Submonoid.powers h)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hh)

/-- The weakly normal schemes of finite type over `k`, in the sense of Stacks Remark 0H5Y: those
schemes `T` of finite type over `k` such that every birational universal homeomorphism `T' ⟶ T` has
a section. -/
def weaklyNormalOfFiniteType : ObjectProperty (LocallyOfFiniteTypeOver (Spec (.of k))) :=
  fun T => QuasiCompact T.obj.hom ∧ Scheme.HasBirationalUniversalHomeomorphismSections T.obj.left

/-- **Stacks Project, Remark 0H5Y, the characteristic `2` example, on weakly normal schemes.**
Let `k` be a field of characteristic `2` and `X = A²_k`. Call a scheme weakly normal if every
birational universal homeomorphism onto it has a section. On the category of weakly normal
schemes of finite type over `k` the functor `S' ↦ z^eff(S' ×_k X / S', 0)` is not representable:
`W = X ×_k X` is normal, hence weakly normal, `Sym²(X)` is normal, and so are their principal
opens (`Stacks.Chow.SymPlane.not_isRepresentable_of_le`). -/
@[stacks 0H5Y "in characteristic 2 the functor is not representable on the category of weakly \
normal schemes of finite type over k"]
theorem not_isRepresentable_weaklyNormal :
    ¬ ((weaklyNormalOfFiniteType k).ι.op ⋙
      effectiveRelativeCyclesFunctor (planeHom k) 0).IsRepresentable := by
  refine not_isRepresentable_of_le k _
    ⟨inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k (ring k))))),
      Scheme.hasBirationalUniversalHomeomorphismSections_spec (ring k)⟩ fun h hh =>
    ⟨⟨inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k (ringAway k h))))),
      ?_⟩, ⟨inferInstanceAs
        (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k (symAway k h))))), ?_⟩⟩
  · have := isDomain_ringAway k hh
    have := isIntegrallyClosed_ringAway k hh
    exact Scheme.hasBirationalUniversalHomeomorphismSections_spec (ringAway k h)
  · have := isDomain_symAway k hh
    have := isIntegrallyClosed_symAway k hh
    exact Scheme.hasBirationalUniversalHomeomorphismSections_spec (symAway k h)

end Stacks.Chow.SymPlane

end
