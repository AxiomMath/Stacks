module

public import StacksCore.FieldTheory.PurelyInseparable.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap

/-!
# Factoring a purely inseparable map of curves into steps of degree the characteristic

Let `k` be a field of characteristic `p > 0` and let `f : X ⟶ Y` be a nonconstant morphism of
proper nonsingular curves over `k` whose extension of function fields `k(Y) ⊆ k(X)` is purely
inseparable. Then `f` factors as a chain
`X = X₀ ⟶ X₁ ⟶ … ⟶ Xₙ = Y` of proper nonsingular curves over `k` in which every step has degree
`p` and every inclusion `k(Xᵢ₊₁) ⊆ k(Xᵢ)` is inseparable.

The proof is the one of the source: a finite purely inseparable extension of fields is a tower of
inseparable extensions of degree `p`, which is [Stacks, Tag 09HI]
(`IsPurelyInseparable.exists_tower_finrank_eq`), and the curve attached to each member of that
tower is supplied by the correspondence between proper nonsingular curves over `k` and finitely
generated extensions of `k` of transcendence degree one, which is [Stacks, Tag 0BY1].

## Main results

* `AlgebraicGeometry.exists_antitone_chain_intermediateField` — a finite purely inseparable
  extension of characteristic exponent `p` is a descending chain of inseparable extensions of
  degree `p`.
* `AlgebraicGeometry.nonempty_functionFieldModel` — every finitely generated extension of `k` of
  transcendence degree one is the function field of a proper nonsingular curve over `k`.
* `AlgebraicGeometry.exists_hom_functionFieldMap_eq` and
  `AlgebraicGeometry.over_hom_ext_of_functionFieldMap` — morphisms over `k` from a normal curve to
  a proper curve correspond to `k`-algebra maps of their function fields.
* `AlgebraicGeometry.exists_chain_isInseparableDegreePrime` — the factorization asserted by the
  source.

## Implementation notes

A nonconstant morphism is a dominant one, the reading used by the correspondence of
[Stacks, Tag 0BY1] in `AlgebraicGeometry.nonconstantOver`. The degree of a morphism of curves is
the degree of its extension of function fields, which is
`AlgebraicGeometry.Scheme.Hom.residueDegree` at the generic point; both forms of the degree of
each step are recorded in the conclusion, together with the inseparability of the extension of
function fields.

The chain is given as a family of curves `Z` indexed by `Fin (n + 1)`, together with the steps
`g`, and with the morphisms `w i : Z i ⟶ Y` which exhibit `f` as the composition along the chain:
the commuting ladder `g i ≫ w i.succ = w i.castSucc` says exactly that `w i` is the composition
of the steps from `Z i` onwards, and `e ≫ w 0 = f` that `f` is the composition of all of them.
The two ends of the chain are the given curves only up to isomorphism — `e` and `w (Fin.last n)`
are isomorphisms — because a curve is determined by its function field only up to isomorphism;
for `n = 0`, where the extension of function fields is trivial, the source's `X = X₀ = Y` is
precisely the assertion that `f` is an isomorphism.

Nothing is carried. Finiteness of the extension of function fields, which the source's appeal to
[Stacks, Tag 09HI] needs, is not a hypothesis: the function field of a variety over `k` is
finitely generated as a field extension of `k`
(`AlgebraicGeometry.varietyFunctionField_essFiniteType`), hence finitely generated over the
intermediate field `k(Y)`, and a purely inseparable extension is algebraic, so
`Algebra.finite_of_essFiniteType_of_isAlgebraic` applies. [Stacks, Tag 0BY1] is used in full,
both halves being available here: the fully faithful functor from normal projective curves to
curves (`AlgebraicGeometry.normalProjectiveCurveToCurveFullyFaithful`) and its essential
surjectivity (`AlgebraicGeometry.normalProjectiveCurveToCurve_essSurj`, an instance).

## References

* [Stacks Project, Tag 0CCX](https://stacks.math.columbia.edu/tag/0CCX)
* [Stacks Project, Tag 0BY1](https://stacks.math.columbia.edu/tag/0BY1)
* [Stacks Project, Tag 09HI](https://stacks.math.columbia.edu/tag/09HI)
-/

@[expose] public noncomputable section

open CategoryTheory IntermediateField

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-! ### Descending towers of purely inseparable extensions -/

/-- If `y ∉ B` and `y ^ p ∈ B`, where `p` is the exponential characteristic, then the simple
extension `B⟮y⟯ / B` is purely inseparable and nontrivial, hence not separable. -/
private lemma not_isSeparable_adjoin_simple {F E : Type u} [Field F] [Field E] [Algebra F E]
    (p : ℕ) [ExpChar F p] {B : IntermediateField F E} {y : E} (hy : y ∉ B) (hyp : y ^ p ∈ B) :
    ¬ Algebra.IsSeparable ↥B ↥(B⟮y⟯) := by
  have : ExpChar ↥B p := expChar_of_injective_algebraMap (algebraMap F ↥B).injective p
  have : IsPurelyInseparable ↥B ↥(B⟮y⟯) :=
    (isPurelyInseparable_adjoin_simple_iff_pow_mem ↥B E p).2 ⟨1, ⟨⟨y ^ p, hyp⟩, by simp⟩⟩
  intro hsep
  have := hsep
  have hbot : B⟮y⟯ = ⊥ := eq_bot_of_isPurelyInseparable_of_isSeparable _
  obtain ⟨b, hb⟩ := IntermediateField.mem_bot.mp
    (hbot ▸ mem_adjoin_simple_self ↥B y : y ∈ (⊥ : IntermediateField ↥B E))
  exact hy (hb ▸ b.2)

/-- One step of a tower: if `D` is `B⟮y⟯` viewed over the base field, with `y ∉ B`, `y ^ p ∈ B`
and `[B⟮y⟯ : B] = p`, then `[D : B] = p` and `D / B` is inseparable. -/
private lemma step_facts {F E : Type u} [Field F] [Field E] [Algebra F E] (p : ℕ) [ExpChar F p]
    {B D : IntermediateField F E} {y : E} (hy : y ∉ B) (hyp : y ^ p ∈ B)
    (hrank : Module.finrank ↥B ↥(B⟮y⟯) = p)
    (hD : restrictScalars F B⟮y⟯ = D) (hle : B ≤ D) :
    letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    Module.finrank ↥B ↥D = p ∧ ¬ Algebra.IsSeparable ↥B ↥D := by
  subst hD
  exact ⟨hrank, not_isSeparable_adjoin_simple p hy hyp⟩

/-- A finite purely inseparable extension `E / F` of characteristic exponent `p` decomposes as a
descending chain `E = A 0 ⊇ A 1 ⊇ ⋯ ⊇ A n = F` of intermediate fields in which every step has
degree `p` and is inseparable. -/
theorem exists_antitone_chain_intermediateField
    (F E : Type u) [Field F] [Field E] [Algebra F E] (p : ℕ) [ExpChar F p]
    [FiniteDimensional F E] [IsPurelyInseparable F E] :
    ∃ (n : ℕ) (A : Fin (n + 1) → IntermediateField F E)
      (hmono : ∀ i j : Fin (n + 1), i ≤ j → A j ≤ A i),
      A 0 = ⊤ ∧ A (Fin.last n) = ⊥ ∧ ∀ i : Fin n,
        letI := (IntermediateField.inclusion
            (hmono i.castSucc i.succ Fin.castSucc_lt_succ.le)).toRingHom.toAlgebra
        Module.finrank ↥(A i.succ) ↥(A i.castSucc) = p ∧
          ¬ Algebra.IsSeparable ↥(A i.succ) ↥(A i.castSucc) := by
  obtain ⟨m, x, hxtop, hx⟩ := IsPurelyInseparable.exists_tower_finrank_eq F E p
  obtain ⟨C, hCdef⟩ : ∃ C : ℕ → IntermediateField F E,
      ∀ j, C j = adjoin F (x '' {l : Fin m | (l : ℕ) < j}) := ⟨_, fun _ => rfl⟩
  have hCmono : ∀ j l : ℕ, j ≤ l → C j ≤ C l := by
    intro j l hjl
    rw [hCdef, hCdef]
    exact adjoin.mono _ _ _ (Set.image_mono fun a ha => lt_of_lt_of_le ha hjl)
  have hCtop : C m = ⊤ := by
    rw [hCdef, show {l : Fin m | (l : ℕ) < m} = Set.univ by ext l; simp, Set.image_univ]
    exact hxtop
  have hCbot : C 0 = ⊥ := by
    rw [hCdef, show {l : Fin m | (l : ℕ) < 0} = (∅ : Set (Fin m)) by ext l; simp,
      Set.image_empty, adjoin_empty]
  have hIio : ∀ (j : ℕ) (hj : j < m), adjoin F (x '' Set.Iio (⟨j, hj⟩ : Fin m)) = C j := by
    intro j hj
    rw [hCdef]
    congr 1
  have hCstep : ∀ (j : ℕ) (hj : j < m),
      restrictScalars F (↥(C j))⟮x ⟨j, hj⟩⟯ = C (j + 1) := by
    intro j hj
    rw [hCdef j, hCdef (j + 1), adjoin_adjoin_left]
    congr 1
    rw [show {l : Fin m | (l : ℕ) < j + 1} = {l : Fin m | (l : ℕ) < j} ∪ {(⟨j, hj⟩ : Fin m)} by
        ext l
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
        omega,
      Set.image_union, Set.image_singleton]
  have key : ∀ (j l : ℕ) (hj : j < m) (hl : l = j + 1) (hle : C j ≤ C l),
      let := (IntermediateField.inclusion hle).toRingHom.toAlgebra
      Module.finrank ↥(C j) ↥(C l) = p ∧ ¬ Algebra.IsSeparable ↥(C j) ↥(C l) := by
    intro j l hj hl hle
    subst hl
    obtain ⟨h1, h2, h3⟩ := hx ⟨j, hj⟩
    rw [hIio j hj] at h1 h2 h3
    exact step_facts p h1 h2 h3 (hCstep j hj) hle
  refine ⟨m, fun i => C (m - (i : ℕ)),
    fun i j hij => hCmono _ _ (Nat.sub_le_sub_left hij m), ?_, ?_, ?_⟩
  · simpa using hCtop
  · simpa using hCbot
  · intro i
    have him : (i : ℕ) < m := i.isLt
    exact key (m - ((i : ℕ) + 1)) (m - (i : ℕ)) (by omega) (by omega) _

/-! ### Curves and the extensions of their function fields -/

/-- The `k`-algebra map of function fields attached to a dominant rational map of varieties is the
extension of function fields of any dominant morphism representing it. -/
theorem fieldHomOfRationalMap_eq_functionFieldMap (V W : Variety k)
    (g : V.toScheme ⟶ W.toScheme) [IsDominant g] (f : V.Hom W)
    (hf : f.toRationalMap = g.toRationalMap) :
    (fieldHomOfRationalMap V W f).toRingHom = functionFieldMap g := by
  suffices h : CommRingCat.ofHom (fieldHomOfRationalMap V W f).toRingHom =
      CommRingCat.ofHom (functionFieldMap g) from congrArg CommRingCat.Hom.hom h
  apply Spec.map_injective
  apply (cancel_mono (W.toScheme.fromSpecStalk (genericPoint W.toScheme))).mp
  rw [fieldHomOfRationalMap_specMap, functionFieldMap_fromSpecStalk, hf]
  simp [Scheme.PartialMap.fromFunctionField, Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap]

/-- A dominant morphism of varieties over `k` induces a map of function fields which is a map of
`k`-algebras. -/
theorem functionFieldMap_algebraMap (V W : Variety k)
    (g : Over.mk V.structureMap ⟶ Over.mk W.structureMap) [IsDominant g.left] (a : k) :
    functionFieldMap g.left (algebraMap k W.toScheme.functionField a) =
      algebraMap k V.toScheme.functionField a := by
  let _ : g.left.IsOver (Spec (.of k)) := ⟨g.w⟩
  let f : V.Hom W := ⟨g.left.toRationalMap⟩
  rw [← fieldHomOfRationalMap_eq_functionFieldMap V W g.left f rfl]
  exact (fieldHomOfRationalMap V W f).commutes a

/-- The extension of function fields induced by a composition of dominant morphisms of integral
schemes is the composition of the induced extensions. -/
theorem functionFieldMap_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z] [IsDominant a] [IsDominant b] :
    functionFieldMap (a ≫ b) = (functionFieldMap a).comp (functionFieldMap b) := by
  suffices h : CommRingCat.ofHom (functionFieldMap (a ≫ b)) =
      CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b)) from
    congrArg CommRingCat.Hom.hom h
  apply Spec.map_injective
  apply (cancel_mono (Z.fromSpecStalk (genericPoint Z))).mp
  rw [functionFieldMap_fromSpecStalk (a ≫ b),
    show CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b)) =
      CommRingCat.ofHom (functionFieldMap b) ≫ CommRingCat.ofHom (functionFieldMap a) from rfl,
    Spec.map_comp, Category.assoc, functionFieldMap_fromSpecStalk b,
    ← Category.assoc (Spec.map (CommRingCat.ofHom (functionFieldMap a))),
    functionFieldMap_fromSpecStalk a]
  exact (Category.assoc _ _ _).symm

/-- The residue degree of a dominant morphism of integral schemes at the generic point is the
degree of the induced extension of function fields. -/
theorem residueDegree_genericPoint_eq_finrank_functionField {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant g] :
    letI : Algebra Y.functionField X.functionField := (functionFieldMap g).toAlgebra
    g.residueDegree (genericPoint X) = Module.finrank Y.functionField X.functionField := by
  let : Algebra Y.functionField X.functionField := (functionFieldMap g).toAlgebra
  let : Algebra (Y.residueField (g (genericPoint X))) (X.residueField (genericPoint X)) :=
    (g.residueFieldMap (genericPoint X)).hom.toAlgebra
  exact (Algebra.finrank_eq_of_equiv_equiv (genericResidueEquivOfDominant g)
    (genericResidueEquiv X) (residueFieldMap_comp_genericResidueEquivOfDominant g).symm).symm

/-- **For a dominant morphism of curves over `k`, the extension of function fields is finite.**
Both function fields are finitely generated extensions of `k` of transcendence degree one
(`AlgebraicGeometry.isCurve_iff_trdeg_functionField_eq_one` and
`AlgebraicGeometry.varietyFunctionField_essFiniteType`), so by additivity of the transcendence
degree in the tower `k ⊆ k(Y) ⊆ k(X)` the extension `k(X)/k(Y)` is algebraic, and `k(X)` is
finitely generated over `k(Y)` because it is over `k`. -/
theorem finiteDimensional_functionField_of_isCurve {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) [IsCurve k pX] [IsCurve k pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) [IsDominant f] :
    letI := (functionFieldMap f).toAlgebra
    FiniteDimensional Y.functionField X.functionField := by
  let VX : Variety k := { toScheme := X, structureMap := pX }
  let VY : Variety k := { toScheme := Y, structureMap := pY }
  let _ : Algebra k X.functionField := varietyFunctionFieldAlgebra VX
  let _ : Algebra k Y.functionField := varietyFunctionFieldAlgebra VY
  let _ : Algebra Y.functionField X.functionField := (functionFieldMap f).toAlgebra
  let F : Over.mk pX ⟶ Over.mk pY := Over.homMk f hf
  let _ : IsDominant F.left := inferInstanceAs (IsDominant f)
  let _ : IsScalarTower k Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => (functionFieldMap_algebraMap VX VY F a).symm
  let _ : Algebra.EssFiniteType k Y.functionField := varietyFunctionField_essFiniteType VY
  let _ : Algebra.EssFiniteType k X.functionField := varietyFunctionField_essFiniteType VX
  let _ : Algebra.EssFiniteType Y.functionField X.functionField :=
    Algebra.EssFiniteType.of_comp k Y.functionField X.functionField
  have htrX : Algebra.trdeg k X.functionField = 1 :=
    (isCurve_iff_trdeg_functionField_eq_one VX).mp inferInstance
  have htrY : Algebra.trdeg k Y.functionField = 1 :=
    (isCurve_iff_trdeg_functionField_eq_one VY).mp inferInstance
  have htower := trdeg_add_eq k Y.functionField (A := X.functionField)
  rw [htrX, htrY] at htower
  have hzero : Algebra.trdeg Y.functionField X.functionField = 0 :=
    Cardinal.add_one_inj.mp (by simpa [add_comm] using htower)
  let _ : Algebra.IsAlgebraic Y.functionField X.functionField := trdeg_eq_zero_iff.mp hzero
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- Every `k`-algebra map `k(W) → k(V)` from the function field of a proper curve to that of a
normal curve is the extension of function fields of a dominant morphism `V ⟶ W` over `k`. -/
theorem exists_hom_functionFieldMap_eq (V W : Variety k)
    [IsCurve k V.structureMap] [IsNormal V.toScheme]
    [IsCurve k W.structureMap] [IsProper W.structureMap]
    (φ : W.toScheme.functionField →ₐ[k] V.toScheme.functionField) :
    ∃ (g : Over.mk V.structureMap ⟶ Over.mk W.structureMap) (f : V.Hom W),
      f.toRationalMap = g.left.toRationalMap ∧ fieldHomOfRationalMap V W f = φ ∧
      ∃ _ : IsDominant g.left, functionFieldMap g.left = φ.toRingHom := by
  obtain ⟨f, hf⟩ := fieldHomOfRationalMap_surjective V W φ
  have _ : IsCurve k (Over.mk V.structureMap).hom := ‹IsCurve k V.structureMap›
  have _ : IsNormal (Over.mk V.structureMap).left := ‹IsNormal V.toScheme›
  have _ : IsVariety k (Over.mk W.structureMap).hom := W.isVariety
  have _ : IsProper (Over.mk W.structureMap).hom := ‹IsProper W.structureMap›
  have _ : IsProperVariety k (Over.mk W.structureMap).hom := IsProperVariety.mk
  obtain ⟨g, hg⟩ := (toRationalMap_bijective k (Over.mk V.structureMap)
    (Over.mk W.structureMap)).surjective ⟨f.toRationalMap, f.isOver⟩
  have hrat : g.left.toRationalMap = f.toRationalMap := congrArg Subtype.val hg
  have hdomR : g.left.toPartialMap.toRationalMap.IsDominant := by
    show g.left.toRationalMap.IsDominant
    rw [hrat]
    exact f.isDominant
  have hdom : IsDominant g.left := by
    have hdomP : IsDominant g.left.toPartialMap.hom :=
      (Scheme.PartialMap.isDominant_toRationalMap_iff _).mp hdomR
    change IsDominant (V.toScheme.topIso.hom ≫ g.left) at hdomP
    exact IsDominant.of_comp V.toScheme.topIso.hom g.left
  refine ⟨g, f, hrat.symm, hf, hdom, ?_⟩
  rw [← hf]
  exact (fieldHomOfRationalMap_eq_functionFieldMap V W g.left f hrat.symm).symm

/-- The rational map of a composition of morphisms of schemes, the first of which is dominant, is
the composition of their rational maps. -/
private lemma toRationalMap_comp_hom {X Y Z : Scheme.{u}} [PreirreducibleSpace X] [Nonempty Y]
    (a : X ⟶ Y) [IsDominant a] (b : Y ⟶ Z) :
    (a ≫ b).toRationalMap = a.toRationalMap.comp b.toRationalMap := by
  show (Scheme.Hom.toPartialMap (a ≫ b)).toRationalMap =
    (Scheme.Hom.toPartialMap a).toRationalMap.comp (Scheme.Hom.toPartialMap b).toRationalMap
  rw [← Scheme.Hom.toPartialMap_compHom, ← Scheme.PartialMap.comp_toPartialMap,
    ← Scheme.RationalMap.toRationalMap_comp]

/-- Composition of rational maps respects equality of the factors. -/
private lemma rationalMap_comp_congr {X Y Z : Scheme.{u}} [PreirreducibleSpace X] [Nonempty Y]
    {a a' : X ⤏ Y} [a.IsDominant] [a'.IsDominant] {b b' : Y ⤏ Z}
    (ha : a = a') (hb : b = b') : a.comp b = a'.comp b' := by
  subst ha hb
  rfl

/-- A morphism over `k` from a normal curve to a proper curve is determined by the induced
`k`-algebra map of function fields. -/
theorem hom_ext_of_fieldHomOfRationalMap_eq (V W : Variety k)
    [IsCurve k V.structureMap] [IsNormal V.toScheme]
    [IsCurve k W.structureMap] [IsProper W.structureMap]
    (g₁ g₂ : Over.mk V.structureMap ⟶ Over.mk W.structureMap)
    (f₁ f₂ : V.Hom W) (h₁ : f₁.toRationalMap = g₁.left.toRationalMap)
    (h₂ : f₂.toRationalMap = g₂.left.toRationalMap)
    (hφ : fieldHomOfRationalMap V W f₁ = fieldHomOfRationalMap V W f₂) : g₁ = g₂ := by
  have _ : IsCurve k (Over.mk V.structureMap).hom := ‹IsCurve k V.structureMap›
  have _ : IsNormal (Over.mk V.structureMap).left := ‹IsNormal V.toScheme›
  have _ : IsVariety k (Over.mk W.structureMap).hom := W.isVariety
  have _ : IsProper (Over.mk W.structureMap).hom := ‹IsProper W.structureMap›
  have _ : IsProperVariety k (Over.mk W.structureMap).hom := IsProperVariety.mk
  apply (toRationalMap_bijective k (Over.mk V.structureMap) (Over.mk W.structureMap)).injective
  apply Subtype.ext
  show g₁.left.toRationalMap = g₂.left.toRationalMap
  rw [← h₁, ← h₂, fieldHomOfRationalMap_injective V W hφ]

/-- A morphism over `k` from a normal curve to a proper curve is determined by the extension of
function fields it induces. -/
theorem over_hom_ext_of_functionFieldMap (V W : Variety k)
    [IsCurve k V.structureMap] [IsNormal V.toScheme]
    [IsCurve k W.structureMap] [IsProper W.structureMap]
    (g₁ g₂ : Over.mk V.structureMap ⟶ Over.mk W.structureMap)
    [IsDominant g₁.left] [IsDominant g₂.left]
    (h : functionFieldMap g₁.left = functionFieldMap g₂.left) : g₁ = g₂ := by
  let _ : g₁.left.IsOver (Spec (.of k)) := ⟨g₁.w⟩
  let _ : g₂.left.IsOver (Spec (.of k)) := ⟨g₂.w⟩
  let f₁ : V.Hom W := ⟨g₁.left.toRationalMap⟩
  let f₂ : V.Hom W := ⟨g₂.left.toRationalMap⟩
  refine hom_ext_of_fieldHomOfRationalMap_eq V W g₁ g₂ f₁ f₂ rfl rfl
    (AlgHom.coe_ringHom_injective ?_)
  rwa [show ((fieldHomOfRationalMap V W f₁ : _ →+* _)) =
      (fieldHomOfRationalMap V W f₁).toRingHom from rfl,
    show ((fieldHomOfRationalMap V W f₂ : _ →+* _)) =
      (fieldHomOfRationalMap V W f₂).toRingHom from rfl,
    fieldHomOfRationalMap_eq_functionFieldMap V W g₁.left f₁ rfl,
    fieldHomOfRationalMap_eq_functionFieldMap V W g₂.left f₂ rfl]

/-- A `k`-isomorphism of the function fields of two normal proper curves over `k` is induced by an
isomorphism of the curves over `k`. -/
theorem exists_isIso_of_algEquiv (V W : Variety k)
    [IsCurve k V.structureMap] [IsNormal V.toScheme] [IsProper V.structureMap]
    [IsCurve k W.structureMap] [IsNormal W.toScheme] [IsProper W.structureMap]
    (φ : W.toScheme.functionField ≃ₐ[k] V.toScheme.functionField) :
    ∃ g : Over.mk V.structureMap ⟶ Over.mk W.structureMap, IsIso g ∧
      ∃ _ : IsDominant g.left, functionFieldMap g.left = φ.toAlgHom.toRingHom := by
  obtain ⟨g, f, hfg, hfφ, hdom, hff⟩ := exists_hom_functionFieldMap_eq V W φ.toAlgHom
  obtain ⟨h, e, heh, heφ, hdom', hee⟩ := exists_hom_functionFieldMap_eq W V φ.symm.toAlgHom
  have hgh : g ≫ h = 𝟙 (Over.mk V.structureMap) := by
    refine hom_ext_of_fieldHomOfRationalMap_eq V V (g ≫ h) (𝟙 _)
      (show V ⟶ V from (f : V ⟶ W) ≫ (e : W ⟶ V)) (𝟙 V : V ⟶ V) ?_ ?_ ?_
    · show f.toRationalMap.comp e.toRationalMap = _
      rw [Over.comp_left, toRationalMap_comp_hom g.left h.left]
      exact rationalMap_comp_congr hfg heh
    · rw [Over.id_left]
      rfl
    · rw [fieldHomOfRationalMap_comp V W V f e, fieldHomOfRationalMap_id, hfφ, heφ]
      exact AlgHom.ext fun x => φ.apply_symm_apply x
  have hhg : h ≫ g = 𝟙 (Over.mk W.structureMap) := by
    refine hom_ext_of_fieldHomOfRationalMap_eq W W (h ≫ g) (𝟙 _)
      (show W ⟶ W from (e : W ⟶ V) ≫ (f : V ⟶ W)) (𝟙 W : W ⟶ W) ?_ ?_ ?_
    · show e.toRationalMap.comp f.toRationalMap = _
      rw [Over.comp_left, toRationalMap_comp_hom h.left g.left]
      exact rationalMap_comp_congr heh hfg
    · rw [Over.id_left]
      rfl
    · rw [fieldHomOfRationalMap_comp W V W e f, fieldHomOfRationalMap_id, hfφ, heφ]
      exact AlgHom.ext fun x => φ.symm_apply_apply x
  exact ⟨g, ⟨h, hgh, hhg⟩, hdom, hff⟩

/-- A morphism over `k` of proper nonsingular curves whose induced extension of function fields
is bijective is an isomorphism. -/
theorem isIso_of_bijective_functionFieldMap (V W : Variety k)
    [IsCurve k V.structureMap] [IsNormal V.toScheme] [IsProper V.structureMap]
    [IsCurve k W.structureMap] [IsNormal W.toScheme] [IsProper W.structureMap]
    (g : Over.mk V.structureMap ⟶ Over.mk W.structureMap) [IsDominant g.left]
    (hbij : Function.Bijective (functionFieldMap g.left)) : IsIso g := by
  let φ : W.toScheme.functionField ≃ₐ[k] V.toScheme.functionField :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (functionFieldMap g.left) hbij)
      fun a => functionFieldMap_algebraMap V W g a
  obtain ⟨g', hiso, hdom', hff'⟩ := exists_isIso_of_algEquiv V W φ
  let : IsDominant g'.left := hdom'
  have hgg' : g = g' := over_hom_ext_of_functionFieldMap V W g g' (by rw [hff']; rfl)
  rwa [hgg']

/-! ### Proper nonsingular models of a function field -/

/-- An isomorphism of varieties over `k` induces an isomorphism of their function fields. -/
def functionFieldAlgEquivOfIso {V W : Variety k} (α : V ≅ W) :
    W.toScheme.functionField ≃ₐ[k] V.toScheme.functionField :=
  AlgEquiv.ofAlgHom (fieldHomOfRationalMap V W α.hom) (fieldHomOfRationalMap W V α.inv)
    (by
      have h := fieldHomOfRationalMap_comp V W V α.hom α.inv
      rw [α.hom_inv_id, fieldHomOfRationalMap_id] at h
      exact h.symm)
    (by
      have h := fieldHomOfRationalMap_comp W V W α.inv α.hom
      rw [α.inv_hom_id, fieldHomOfRationalMap_id] at h
      exact h.symm)

/-- A proper nonsingular curve over `k` together with an identification of its function field with
a given extension of `k`. -/
structure FunctionFieldModel (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K] where
  /-- The underlying curve. -/
  variety : Variety k
  /-- It is a curve over `k`. -/
  isCurve : IsCurve k variety.structureMap
  /-- It is proper over `k`. -/
  isProper : IsProper variety.structureMap
  /-- It is nonsingular. -/
  isRegular : IsRegular variety.toScheme
  /-- Its function field is the given extension of `k`. -/
  equiv : variety.toScheme.functionField ≃ₐ[k] K

/-- A curve over `k` isomorphic, as a variety, to a normal projective curve has a proper
nonsingular model of its function field. -/
private theorem nonempty_functionFieldModel_of_iso (K : Type u) [Field K] [Algebra k K]
    {W V₀ : Variety k} (hcurve : IsCurve k W.structureMap)
    (hproj : IsProjectiveMorphism W.structureMap) (hnormal : IsNormal W.toScheme)
    (β : W ≅ V₀) (e₀ : V₀.toScheme.functionField ≃ₐ[k] K) :
    Nonempty (FunctionFieldModel k K) := by
  let : IsCurve k W.structureMap := hcurve
  exact ⟨{ variety := W
           isCurve := hcurve
           isProper := isProper_of_isProjectiveMorphism _ hproj
           isRegular := (isRegular_iff_isNormal_of_isCurve k W.structureMap).mpr hnormal
           equiv := (functionFieldAlgEquivOfIso β).symm.trans e₀ }⟩

/-- Every finitely generated extension of `k` of transcendence degree one is the function field of
a proper nonsingular curve over `k`: the affine model of the extension is a curve, and
`AlgebraicGeometry.normalProjectiveCurveToCurve_essSurj` makes it isomorphic, as a variety under
dominant rational maps, to a normal projective one. -/
theorem nonempty_functionFieldModel (K : Type u) [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) : Nonempty (FunctionFieldModel k K) := by
  let KObj : FinitelyGeneratedFieldExtension k :=
    ⟨CommAlgCat.of k K, ⟨Field.toIsField K, inferInstance⟩⟩
  let V₀ : Variety k := affineModelOfFieldExtension KObj
  have e₀ : V₀.toScheme.functionField ≃ₐ[k] K := affineModelFunctionFieldAlgEquivOver KObj
  have hcurve : IsCurve k V₀.structureMap := by
    rwa [isCurve_iff_trdeg_functionField_eq_one V₀, e₀.trdeg_eq]
  let C : Curve k := ⟨V₀, hcurve⟩
  let P := (normalProjectiveCurveToCurve k).objPreimage C
  obtain ⟨hPcurve, hPproj, hPnormal⟩ := P.property
  exact nonempty_functionFieldModel_of_iso K hPcurve hPproj hPnormal
    ((ObjectProperty.ι (Variety.IsCurveProperty k)).mapIso
      ((normalProjectiveCurveToCurve k).objObjPreimageIso C)) e₀

/-! ### The factorization into steps of degree the characteristic -/

/-- A proper nonsingular curve over `k`. -/
structure ProperNonsingularCurve (k : Type u) [Field k] where
  /-- The underlying scheme over `Spec k`. -/
  obj : Over (Spec (.of k))
  /-- It is a curve over `k`. -/
  isCurve : IsCurve k obj.hom
  /-- It is proper over `k`. -/
  isProper : IsProper obj.hom
  /-- It is nonsingular. -/
  isRegular : IsRegular obj.left

attribute [instance] ProperNonsingularCurve.isCurve ProperNonsingularCurve.isProper

/-- Equal ring homomorphisms give the same degree and the same separability. -/
private theorem finrank_and_not_isSeparable_congr {R S : Type u} [Field R] [Field S]
    {ι₁ ι₂ : R →+* S} (h : ι₁ = ι₂) (q : ℕ)
    (h1 : letI := ι₂.toAlgebra; Module.finrank R S = q)
    (h2 : letI := ι₂.toAlgebra; ¬ Algebra.IsSeparable R S) :
    letI := ι₁.toAlgebra
    Module.finrank R S = q ∧ ¬ Algebra.IsSeparable R S := by
  subst h
  exact ⟨h1, h2⟩

/-- The chain of proper nonsingular models of a finite purely inseparable extension of
finitely generated extensions of `k` of transcendence degree one. -/
private theorem exists_chain_models (p : ℕ) (KY KX : Type u) [Field KY] [Field KX]
    [Algebra k KY] [Algebra k KX] [Algebra KY KX] [IsScalarTower k KY KX]
    [Algebra.EssFiniteType k KY] [ExpChar KY p]
    [FiniteDimensional KY KX] [IsPurelyInseparable KY KX] (htrKX : Algebra.trdeg k KX = 1) :
    ∃ (n : ℕ) (V : Fin (n + 1) → Variety k)
      (_ : ∀ i, IsCurve k (V i).structureMap ∧ IsProper (V i).structureMap ∧
        IsRegular (V i).toScheme)
      (ψ : ∀ i : Fin n, (V i.succ).toScheme.functionField →ₐ[k]
        (V i.castSucc).toScheme.functionField)
      (θ : ∀ i : Fin (n + 1), KY →ₐ[k] (V i).toScheme.functionField)
      (ε : (V 0).toScheme.functionField ≃ₐ[k] KX),
      (∀ i : Fin n, (ψ i).comp (θ i.succ) = θ i.castSucc) ∧
      (∀ a : KY, ε (θ 0 a) = algebraMap KY KX a) ∧
      Function.Bijective (θ (Fin.last n)) ∧
      ∀ i : Fin n,
        letI := (ψ i).toRingHom.toAlgebra
        Module.finrank (V i.succ).toScheme.functionField
            (V i.castSucc).toScheme.functionField = p ∧
          ¬ Algebra.IsSeparable (V i.succ).toScheme.functionField
            (V i.castSucc).toScheme.functionField := by
  obtain ⟨n, A, hmono, hA0, hAn, hstepfacts⟩ := exists_antitone_chain_intermediateField KY KX p
  have htr : ∀ i : Fin (n + 1), Algebra.trdeg k ↥(A i) = 1 := by
    intro i
    have : IsScalarTower k ↥(A i) KX := IsScalarTower.of_algebraMap_eq fun a => rfl
    have hz : Algebra.trdeg ↥(A i) KX = 0 := trdeg_eq_zero
    have h := trdeg_add_eq k ↥(A i) (A := KX)
    rw [hz, add_zero, htrKX] at h
    exact h
  have hmodel : ∀ i : Fin (n + 1), Nonempty (FunctionFieldModel k ↥(A i)) := by
    intro i
    have : Algebra.EssFiniteType k ↥(A i) := Algebra.EssFiniteType.comp k KY ↥(A i)
    exact nonempty_functionFieldModel ↥(A i) (htr i)
  let M : ∀ i : Fin (n + 1), FunctionFieldModel k ↥(A i) := fun i => (hmodel i).some
  let incl : ∀ i : Fin n, ↥(A i.succ) →ₐ[k] ↥(A i.castSucc) := fun i =>
    (IntermediateField.inclusion
      (hmono i.castSucc i.succ Fin.castSucc_lt_succ.le)).restrictScalars k
  let ψ : ∀ i : Fin n, (M i.succ).variety.toScheme.functionField →ₐ[k]
      (M i.castSucc).variety.toScheme.functionField := fun i =>
    ((M i.castSucc).equiv.symm.toAlgHom.comp (incl i)).comp (M i.succ).equiv.toAlgHom
  let θ : ∀ i : Fin (n + 1), KY →ₐ[k] (M i).variety.toScheme.functionField := fun i =>
    (M i).equiv.symm.toAlgHom.comp ((Algebra.ofId KY ↥(A i)).restrictScalars k)
  let ε : (M 0).variety.toScheme.functionField ≃ₐ[k] KX :=
    (M 0).equiv.trans
      (((IntermediateField.equivOfEq hA0).trans IntermediateField.topEquiv).restrictScalars k)
  have hladder : ∀ i : Fin n, (ψ i).comp (θ i.succ) = θ i.castSucc := by
    intro i
    refine AlgHom.ext fun a => ?_
    show (M i.castSucc).equiv.symm (incl i ((M i.succ).equiv ((M i.succ).equiv.symm
      (Algebra.ofId KY ↥(A i.succ) a)))) = (M i.castSucc).equiv.symm
        (Algebra.ofId KY ↥(A i.castSucc) a)
    rw [AlgEquiv.apply_symm_apply]
    exact congrArg (M i.castSucc).equiv.symm (Subtype.ext rfl)
  have hstart : ∀ a : KY, ε (θ 0 a) = algebraMap KY KX a := by
    intro a
    show IntermediateField.topEquiv (IntermediateField.equivOfEq hA0
      ((M 0).equiv ((M 0).equiv.symm (Algebra.ofId KY ↥(A 0) a)))) = algebraMap KY KX a
    rw [AlgEquiv.apply_symm_apply]
    rfl
  have hofIdBij : Function.Bijective (Algebra.ofId KY ↥(A (Fin.last n))) := by
    refine ⟨(algebraMap KY ↥(A (Fin.last n))).injective, fun y => ?_⟩
    have hy : (y : KX) ∈ (⊥ : IntermediateField KY KX) := hAn ▸ y.2
    rw [IntermediateField.mem_bot] at hy
    obtain ⟨a, ha⟩ := hy
    exact ⟨a, Subtype.ext ha⟩
  have hend : Function.Bijective (θ (Fin.last n)) :=
    (M (Fin.last n)).equiv.symm.bijective.comp hofIdBij
  have hdeg : ∀ i : Fin n,
      let := (ψ i).toRingHom.toAlgebra
      Module.finrank (M i.succ).variety.toScheme.functionField
          (M i.castSucc).variety.toScheme.functionField = p ∧
        ¬ Algebra.IsSeparable (M i.succ).variety.toScheme.functionField
          (M i.castSucc).variety.toScheme.functionField := by
    intro i
    obtain ⟨hA, hB⟩ := hstepfacts i
    let : Algebra ↥(A i.succ) ↥(A i.castSucc) := (IntermediateField.inclusion
      (hmono i.castSucc i.succ Fin.castSucc_lt_succ.le)).toRingHom.toAlgebra
    let : Algebra (M i.succ).variety.toScheme.functionField
        (M i.castSucc).variety.toScheme.functionField := (ψ i).toRingHom.toAlgebra
    have hcompat : (algebraMap ↥(A i.succ) ↥(A i.castSucc)).comp
        (M i.succ).equiv.toRingEquiv.toRingHom =
        (M i.castSucc).equiv.toRingEquiv.toRingHom.comp
          (algebraMap (M i.succ).variety.toScheme.functionField
            (M i.castSucc).variety.toScheme.functionField) := by
      refine RingHom.ext fun a => ?_
      show incl i ((M i.succ).equiv a) =
        (M i.castSucc).equiv ((M i.castSucc).equiv.symm (incl i ((M i.succ).equiv a)))
      rw [AlgEquiv.apply_symm_apply]
    refine ⟨?_, ?_⟩
    · rw [Algebra.finrank_eq_of_equiv_equiv (M i.succ).equiv.toRingEquiv
        (M i.castSucc).equiv.toRingEquiv hcompat]
      exact hA
    · intro hsep
      let := hsep
      exact hB (Algebra.IsSeparable.of_equiv_equiv (M i.succ).equiv.toRingEquiv
        (M i.castSucc).equiv.toRingEquiv hcompat)
  exact ⟨n, fun i => (M i).variety,
    fun i => ⟨(M i).isCurve, (M i).isProper, (M i).isRegular⟩, ψ, θ, ε,
    hladder, hstart, hend, hdeg⟩

/-- A `k`-algebra map from the function field of a proper curve to that of a nonsingular curve is
the extension of function fields of a dominant morphism over `k`. -/
private theorem exists_dominant_functionFieldMap_eq (V W : Variety k)
    (hV : IsCurve k V.structureMap ∧ IsProper V.structureMap ∧ IsRegular V.toScheme)
    (hWc : IsCurve k W.structureMap) (hWp : IsProper W.structureMap)
    (φ : W.toScheme.functionField →ₐ[k] V.toScheme.functionField) :
    ∃ g : Over.mk V.structureMap ⟶ Over.mk W.structureMap,
      ∃ _ : IsDominant g.left, functionFieldMap g.left = φ.toRingHom := by
  let := hV.1
  let : IsNormal V.toScheme := isNormal_of_isRegular _ hV.2.2
  obtain ⟨g, -, -, -, hd, hff⟩ := exists_hom_functionFieldMap_eq V W φ
  exact ⟨g, hd, hff⟩

/-- A morphism over `k` of proper nonsingular curves inducing a bijection of function fields is an
isomorphism. -/
private theorem isIso_of_bijective_functionFieldMap_of_isRegular (V W : Variety k)
    (hV : IsCurve k V.structureMap ∧ IsProper V.structureMap ∧ IsRegular V.toScheme)
    (hW : IsCurve k W.structureMap ∧ IsProper W.structureMap ∧ IsRegular W.toScheme)
    (g : Over.mk V.structureMap ⟶ Over.mk W.structureMap) [IsDominant g.left]
    (hbij : Function.Bijective (functionFieldMap g.left)) : IsIso g := by
  let := hV.1
  let := hV.2.1
  let : IsNormal V.toScheme := isNormal_of_isRegular _ hV.2.2
  let := hW.1
  let := hW.2.1
  let : IsNormal W.toScheme := isNormal_of_isRegular _ hW.2.2
  exact isIso_of_bijective_functionFieldMap V W g hbij

/-- A morphism over `k` from a normal curve to a proper curve is the composite `a ≫ b` as soon as
its extension of function fields is the composite of those of `a` and `b`. -/
private theorem comp_eq_of_functionFieldMap_comp (V W Z : Variety k)
    [IsCurve k V.structureMap] [IsNormal V.toScheme]
    [IsCurve k Z.structureMap] [IsProper Z.structureMap]
    (a : Over.mk V.structureMap ⟶ Over.mk W.structureMap)
    (b : Over.mk W.structureMap ⟶ Over.mk Z.structureMap)
    (c : Over.mk V.structureMap ⟶ Over.mk Z.structureMap)
    [IsDominant a.left] [IsDominant b.left] [IsDominant c.left]
    (h : (functionFieldMap a.left).comp (functionFieldMap b.left) = functionFieldMap c.left) :
    a ≫ b = c := by
  let : IsDominant (a ≫ b).left := inferInstanceAs (IsDominant (a.left ≫ b.left))
  exact over_hom_ext_of_functionFieldMap V Z (a ≫ b) c
    ((functionFieldMap_comp a.left b.left).trans h)

/-- The factorization of Stacks 0CCX for curves presented as varieties over `k`. -/
private theorem exists_chain_aux (p : ℕ) [Fact p.Prime] [CharP k p] (VX VY : Variety k)
    [IsCurve k VX.structureMap] [IsProper VX.structureMap] (hXreg : IsRegular VX.toScheme)
    [IsCurve k VY.structureMap] [IsProper VY.structureMap] (hYreg : IsRegular VY.toScheme)
    (f : Over.mk VX.structureMap ⟶ Over.mk VY.structureMap) [IsDominant f.left]
    (hpure : letI : Algebra VY.toScheme.functionField VX.toScheme.functionField :=
        (functionFieldMap f.left).toAlgebra
      IsPurelyInseparable VY.toScheme.functionField VX.toScheme.functionField) :
    ∃ (n : ℕ) (Z : Fin (n + 1) → ProperNonsingularCurve k)
      (g : ∀ i : Fin n, (Z i.castSucc).obj ⟶ (Z i.succ).obj)
      (w : ∀ i : Fin (n + 1), (Z i).obj ⟶ Over.mk VY.structureMap)
      (e : Over.mk VX.structureMap ⟶ (Z 0).obj),
      IsIso e ∧ IsIso (w (Fin.last n)) ∧ e ≫ w 0 = f ∧
      (∀ i : Fin n, g i ≫ w i.succ = w i.castSucc) ∧
      ∀ i : Fin n, ∃ hdom : IsDominant (g i).left,
        letI : IsDominant (g i).left := hdom
        letI : Algebra (Z i.succ).obj.left.functionField
            (Z i.castSucc).obj.left.functionField := (functionFieldMap (g i).left).toAlgebra
        Module.finrank (Z i.succ).obj.left.functionField
            (Z i.castSucc).obj.left.functionField = p ∧
          ¬ Algebra.IsSeparable (Z i.succ).obj.left.functionField
            (Z i.castSucc).obj.left.functionField ∧
          (g i).left.residueDegree (genericPoint (Z i.castSucc).obj.left) = p := by
  classical
  let : IsNormal VX.toScheme := isNormal_of_isRegular _ hXreg
  let : IsNormal VY.toScheme := isNormal_of_isRegular _ hYreg
  let : Algebra VY.toScheme.functionField VX.toScheme.functionField :=
    (functionFieldMap f.left).toAlgebra
  let : IsScalarTower k VY.toScheme.functionField VX.toScheme.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => (functionFieldMap_algebraMap VX VY f a).symm
  let : IsPurelyInseparable VY.toScheme.functionField VX.toScheme.functionField := hpure
  let : CharP VY.toScheme.functionField p :=
    charP_of_injective_algebraMap (algebraMap k VY.toScheme.functionField).injective p
  let : ExpChar VY.toScheme.functionField p := ExpChar.prime Fact.out
  let : Algebra.EssFiniteType k VY.toScheme.functionField :=
    varietyFunctionField_essFiniteType VY
  let : FiniteDimensional VY.toScheme.functionField VX.toScheme.functionField :=
    finiteDimensional_functionField_of_isCurve VX.structureMap VY.structureMap f.left
      (Over.w f)
  have htrKX : Algebra.trdeg k VX.toScheme.functionField = 1 :=
    (isCurve_iff_trdeg_functionField_eq_one VX).mp inferInstance
  obtain ⟨n, V, hV, ψ, θ, ε, hladder, hstart, hend, hdeg⟩ := exists_chain_models p
    VY.toScheme.functionField VX.toScheme.functionField htrKX
  have hgex : ∀ i : Fin n, ∃ g : Over.mk (V i.castSucc).structureMap ⟶
      Over.mk (V i.succ).structureMap,
      ∃ _ : IsDominant g.left, functionFieldMap g.left = (ψ i).toRingHom := fun i =>
    exists_dominant_functionFieldMap_eq _ _ (hV i.castSucc) (hV i.succ).1 (hV i.succ).2.1 (ψ i)
  choose g hgdom hgff using hgex
  have hwex : ∀ i : Fin (n + 1), ∃ w : Over.mk (V i).structureMap ⟶ Over.mk VY.structureMap,
      ∃ _ : IsDominant w.left, functionFieldMap w.left = (θ i).toRingHom := fun i =>
    exists_dominant_functionFieldMap_eq _ _ (hV i) inferInstance inferInstance (θ i)
  choose w hwdom hwff using hwex
  obtain ⟨e, hedom, heff⟩ : ∃ e : Over.mk VX.structureMap ⟶ Over.mk (V 0).structureMap,
      ∃ _ : IsDominant e.left, functionFieldMap e.left = ε.toAlgHom.toRingHom :=
    exists_dominant_functionFieldMap_eq _ _ ⟨inferInstance, inferInstance, hXreg⟩ (hV 0).1
      (hV 0).2.1 ε.toAlgHom
  refine ⟨n, fun i => ⟨Over.mk (V i).structureMap, (hV i).1, (hV i).2.1, (hV i).2.2⟩,
    g, w, e, ?_, ?_, ?_, ?_, ?_⟩
  · let := hedom
    exact isIso_of_bijective_functionFieldMap_of_isRegular VX (V 0) ⟨inferInstance, inferInstance,
      hXreg⟩ (hV 0) e (by rw [heff]; exact ε.bijective)
  · let := hwdom (Fin.last n)
    exact isIso_of_bijective_functionFieldMap_of_isRegular (V (Fin.last n)) VY (hV _)
      ⟨inferInstance, inferInstance, hYreg⟩ (w (Fin.last n)) (by rw [hwff]; exact hend)
  · let := hedom
    let := hwdom 0
    refine comp_eq_of_functionFieldMap_comp VX (V 0) VY e (w 0) f ?_
    rw [heff, hwff 0]
    exact RingHom.ext fun a => hstart a
  · intro i
    obtain ⟨hc, hp, hr⟩ := hV i.castSucc
    let := hc
    let : IsNormal (V i.castSucc).toScheme := isNormal_of_isRegular _ hr
    let := hgdom i
    let := hwdom i.succ
    let := hwdom i.castSucc
    refine comp_eq_of_functionFieldMap_comp (V i.castSucc) (V i.succ) VY (g i) (w i.succ)
      (w i.castSucc) ?_
    rw [hgff i, hwff i.succ, hwff i.castSucc]
    exact RingHom.ext fun a => DFunLike.congr_fun (hladder i) a
  · intro i
    refine ⟨hgdom i, ?_⟩
    let := hgdom i
    obtain ⟨hfr, hns⟩ := finrank_and_not_isSeparable_congr (hgff i) p (hdeg i).1 (hdeg i).2
    exact ⟨hfr, hns, (residueDegree_genericPoint_eq_finrank_functionField (g i).left).trans hfr⟩

/-- **Stacks Project, Tag 0CCX.** Let `k` be a field of characteristic `p`. A nonconstant
morphism `f` of proper nonsingular curves over `k` whose extension of function fields is purely
inseparable factors as a chain of proper nonsingular curves over `k` in which every step has
degree `p` and induces an inseparable extension of function fields. -/
@[stacks 0CCX "the factorization into steps of degree p"]
theorem exists_chain_isInseparableDegreePrime (p : ℕ) [Fact p.Prime] [CharP k p] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] [IsProper pX] [IsProper pY]
    (hXreg : IsRegular X) (hYreg : IsRegular Y)
    (f : Over.mk pX ⟶ Over.mk pY) [IsDominant f.left]
    (hpure : letI : Algebra Y.functionField X.functionField :=
        (functionFieldMap f.left).toAlgebra
      IsPurelyInseparable Y.functionField X.functionField) :
    ∃ (n : ℕ) (Z : Fin (n + 1) → ProperNonsingularCurve k)
      (g : ∀ i : Fin n, (Z i.castSucc).obj ⟶ (Z i.succ).obj)
      (w : ∀ i : Fin (n + 1), (Z i).obj ⟶ Over.mk pY)
      (e : Over.mk pX ⟶ (Z 0).obj),
      IsIso e ∧ IsIso (w (Fin.last n)) ∧ e ≫ w 0 = f ∧
      (∀ i : Fin n, g i ≫ w i.succ = w i.castSucc) ∧
      ∀ i : Fin n, ∃ hdom : IsDominant (g i).left,
        letI : IsDominant (g i).left := hdom
        letI : Algebra (Z i.succ).obj.left.functionField
            (Z i.castSucc).obj.left.functionField := (functionFieldMap (g i).left).toAlgebra
        Module.finrank (Z i.succ).obj.left.functionField
            (Z i.castSucc).obj.left.functionField = p ∧
          ¬ Algebra.IsSeparable (Z i.succ).obj.left.functionField
            (Z i.castSucc).obj.left.functionField ∧
          (g i).left.residueDegree (genericPoint (Z i.castSucc).obj.left) = p :=
  exists_chain_aux p ⟨X, pX⟩ ⟨Y, pY⟩ hXreg hYreg f hpure

end AlgebraicGeometry

end
