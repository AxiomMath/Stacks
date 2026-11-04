module

public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafPushforwardNormal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceSections
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local principality of divisors on a smooth curve, and exactness in the middle

The surjectivity and middle-exactness inputs of Stacks 03RI on sections, built on
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceSections`:

* `Stacks.EtaleCohomology.exists_opens_ord_eq_of_finite_support`: **a divisor on a smooth curve is
  locally the divisor of a rational function**, which is the surjectivity step of the source's
  proof.
* `Stacks.EtaleCohomology.isClosed_singleton_of_isCurve`: every non-generic point of a curve is
  closed, so the divisor's support is a closed set that an open neighbourhood avoids.
* `Stacks.EtaleCohomology.exists_units_functionField_ord_eq_one`: a uniformizer at a non-generic
  point of a smooth curve, the one place where smoothness and the discrete valuation enter.
* `Stacks.EtaleCohomology.exists_restrict_eq_of_genericFibreDivisorSections_eq_zero`: **exactness
  in the middle**, on sections over an irreducible étale neighbourhood of a smooth curve — a
  section of `j_* 𝐆_{m,η}` with vanishing divisor is the restriction of an invertible global
  function.
* `Stacks.EtaleCohomology.injective_genericFibreToFunctionField`: the generic fibre of an
  integral étale `X`-scheme being a one-point space, reading its global functions as rational
  functions on `X` loses nothing.
* `Stacks.EtaleCohomology.isNormal_of_smooth_isCurve`: a smooth curve is normal, which is what
  makes algebraic Hartogs available.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Order TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology


/-! ### A divisor on a smooth curve is locally the divisor of a rational function -/

section Generic

variable (Y : Scheme.{u}) [IrreducibleSpace Y]

/-- **The generic point of an irreducible scheme has codimension zero**: it is the greatest point
in the specialization order. -/
theorem coheight_genericPoint_eq_zero : coheight (genericPoint Y) = 0 :=
  Order.coheight_eq_zero.2 fun b _ => le_iff_specializes.2 (genericPoint_specializes b)

end Generic

section LocalPrincipal

variable {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [IsCurve k f]

/-- **Every point of a curve other than the generic point is closed.** This specialises
`Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint` to a curve,
whose topological Krull dimension is one. -/
theorem isClosed_singleton_of_isCurve {x : Y} (hx : x ≠ genericPoint Y) :
    IsClosed ({x} : Set Y) :=
  Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint Y
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)) hx

/-- **A finitely supported family of integers, trivial at the generic point, vanishes on an open
neighbourhood of `x` away from `x`**: the rest of its support is a finite set of closed points. -/
private theorem exists_opens_forall_eq_zero_of_finite_support {D : Y → ℤ}
    (hD : {y : Y | D y ≠ 0}.Finite) (hDgen : D (genericPoint Y) = 0) (x : Y) :
    ∃ V : Y.Opens, x ∈ V ∧ ∀ y ∈ V, y ≠ x → D y = 0 := by
  have hcl : IsClosed ({y : Y | D y ≠ 0} \ {x}) := by
    rw [← Set.biUnion_of_singleton ({y : Y | D y ≠ 0} \ {x})]
    exact (hD.subset Set.sdiff_subset).isClosed_biUnion fun y hy =>
      isClosed_singleton_of_isCurve f fun h => hy.1 (h ▸ hDgen)
  exact ⟨⟨_, hcl.isOpen_compl⟩, fun h => h.2 rfl, fun y hy hyx => by
    by_contra hc
    exact hy ⟨hc, by simpa using hyx⟩⟩

variable [Smooth f] [IsLocallyNoetherian Y]

/-- **A uniformizer at a non-generic point of a smooth curve**: an invertible rational function
whose order of vanishing there is one. Smoothness is what makes the local ring a discrete
valuation ring, hence its valuation surjective onto `ℤ`. -/
theorem exists_units_functionField_ord_eq_one {x : Y} (hx : x ≠ genericPoint Y) :
    ∃ g : (↥Y.functionField)ˣ, Scheme.ord (g : ↥Y.functionField) x = 1 := by
  have hx1 : coheight x = 1 := IsCurve.coheight_eq_one f hx
  have : IsDiscreteValuationRing (Y.presheaf.stalk x) :=
    IsCurve.isDiscreteValuationRing_stalk k f hx
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk x) := krullDimLE_of_coheight_le hx1.le
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk x)
  have hne : algebraMap (Y.presheaf.stalk x) Y.functionField ϖ ≠ 0 := fun h =>
    hϖ.ne_zero (IsFractionRing.injective (Y.presheaf.stalk x) Y.functionField (by simpa using h))
  refine ⟨Units.mk0 _ hne, ?_⟩
  rw [Units.val_mk0, Scheme.ord_eq_iff hx1 hne]
  show Scheme.ordHom x hx1 _ = _
  have hord : Scheme.ordHom x hx1 = Ring.ordFrac (Y.presheaf.stalk x) := rfl
  rw [hord, Ring.ordFrac_eq_ord (R := ↥(Y.presheaf.stalk x)) (K := ↥Y.functionField)
    hϖ.ne_zero, Ring.ordMonoidWithZeroHom_eq_coe (R := ↥(Y.presheaf.stalk x))
    (mem_nonZeroDivisors_iff_ne_zero.2 hϖ.ne_zero) (n := 1)
    (by simpa using Ring.ord_of_irreducible hϖ)]
  simp

/-- **The divisor `n · x` on a smooth curve is principal near `x`**: a power of a uniformizer has
order of vanishing `n` at `x`, and its remaining zeros and poles are finitely many closed points,
which an open neighbourhood of `x` avoids. -/
theorem exists_opens_ord_eq_single {x : Y} (hx : x ≠ genericPoint Y) (n : ℤ) :
    ∃ (V : Y.Opens) (g : (↥Y.functionField)ˣ), x ∈ V ∧
      Scheme.ord (g : ↥Y.functionField) x = n ∧
      ∀ y ∈ V, y ≠ x → Scheme.ord (g : ↥Y.functionField) y = 0 := by
  obtain ⟨g₀, hg₀⟩ := exists_units_functionField_ord_eq_one f hx
  have hordg : ∀ y : Y, Scheme.ord ((g₀ ^ n : (↥Y.functionField)ˣ) : ↥Y.functionField) y =
      n * Scheme.ord (g₀ : ↥Y.functionField) y := by
    intro y
    have h := (Scheme.ordAddMonoidHom (X := Y) y).map_zsmul n (Additive.ofMul g₀)
    rw [Scheme.ordAddMonoidHom_apply, Scheme.ordAddMonoidHom_apply] at h
    simpa [toMul_zsmul, smul_eq_mul] using h
  have hfin : {y : Y |
      Scheme.ord ((g₀ ^ n : (↥Y.functionField)ˣ) : ↥Y.functionField) y ≠ 0}.Finite :=
    IsCurve.finite_support_ord f ((g₀ ^ n : (↥Y.functionField)ˣ) : ↥Y.functionField)
  obtain ⟨V, hxV, hV⟩ := exists_opens_forall_eq_zero_of_finite_support f hfin
    (Scheme.ord_eq_zero_of_coheight_neq_one (by rw [coheight_genericPoint_eq_zero Y]; simp) _) x
  exact ⟨V, g₀ ^ n, hxV, by rw [hordg, hg₀, mul_one], hV⟩

/-- **A divisor on a smooth curve is locally the divisor of a rational function.** Around any
point there is a Zariski open on which the given finitely supported family of integers is the
family of orders of vanishing of an invertible rational function.

This is the surjectivity step in the proof of Stacks 03RI: the third map of the fundamental exact
sequence is surjective because a divisor on a nonsingular curve is locally principal. -/
theorem exists_opens_ord_eq_of_finite_support (D : Y → ℤ) (hD : {y : Y | D y ≠ 0}.Finite)
    (hDgen : D (genericPoint Y) = 0) (x : Y) :
    ∃ (V : Y.Opens) (g : (↥Y.functionField)ˣ), x ∈ V ∧
      ∀ y ∈ V, Scheme.ord (g : ↥Y.functionField) y = D y := by
  obtain ⟨W, hxW, hW⟩ := exists_opens_forall_eq_zero_of_finite_support f hD hDgen x
  by_cases hx : x = genericPoint Y
  · refine ⟨W, 1, hxW, fun y hy => ?_⟩
    rw [Units.val_one, Scheme.ord_one]
    by_cases hyx : y = x
    · rw [hyx, hx, hDgen]
    · exact (hW y hy hyx).symm
  · obtain ⟨V, g, hxV, hgx, hgy⟩ := exists_opens_ord_eq_single f hx (D x)
    refine ⟨V ⊓ W, g, ⟨hxV, hxW⟩, fun y hy => ?_⟩
    by_cases hyx : y = x
    · rw [hyx]; exact hgx
    · rw [hgy y hy.1 hyx, hW y hy.2 hyx]

end LocalPrincipal

/-! ### Exactness in the middle, on sections over an irreducible étale neighbourhood -/

section Normal

variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- **A smooth curve is a normal scheme.** At a non-generic point the local ring is a discrete
valuation ring, hence integrally closed, and the local ring at the generic point is the function
field. -/
@[ega "IV 11.3.13" "(ii), special case"]
theorem isNormal_of_smooth_isCurve (f : Y ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] :
    AlgebraicGeometry.IsNormal Y := by
  refine (AlgebraicGeometry.isNormal_iff_stalk_normal Y).2 fun x => ⟨inferInstance, ?_⟩
  by_cases hx : x = genericPoint Y
  · subst hx
    exact inferInstanceAs (IsIntegrallyClosed ↥Y.functionField)
  · have hdvr : IsDiscreteValuationRing ↑(Y.presheaf.stalk x) :=
      IsCurve.isDiscreteValuationRing_stalk k f hx
    have hnorm : IsNormalRing ↑(Y.presheaf.stalk x) :=
      ((isDiscreteValuationRing_stalk_tfae_of_isCurve k f
        (isClosed_singleton_of_isCurve f hx)).out 3 2).mp hdvr
    exact hnorm.of_isLocalRing.2

end Normal

section Fibre

/-- **A point of an irreducible scheme lying over the generic point of an irreducible target is
the generic point.** The fibres of a locally quasi-finite morphism are discrete, so they carry no
specialization, and the generic point of the source already lies over the generic point of the
target by flatness. -/
theorem eq_genericPoint_of_base_eq_genericPoint {X V : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace V] (g : V ⟶ X) [Flat g] [LocallyQuasiFinite g] {y : V}
    (hy : g y = genericPoint X) : y = genericPoint V := by
  have hgen : g (genericPoint V) = genericPoint X :=
    base_genericPoint_eq_genericPoint_of_flat g
  refine ((g.isDiscrete_preimage_singleton (g (genericPoint V))).eq_of_specializes
    (genericPoint_specializes y) rfl ?_).symm
  exact Set.mem_preimage.2 (Set.mem_singleton_iff.2 (hy.trans hgen.symm))

/-- **On a one-point scheme a global section is determined by its germ.** Two sections with the
same germ agree on a neighbourhood of the point, and the only such neighbourhood is everything. -/
theorem injective_germ_top_of_subsingleton {V : Scheme.{u}} [Subsingleton ↥V] (z : V) :
    Function.Injective (V.presheaf.germ ⊤ z trivial) := fun s t hst => by
  obtain ⟨W, hzW, iU, iV, h⟩ :=
    V.presheaf.germ_eq (U := ⊤) (V := ⊤) z trivial trivial s t hst
  have hW : W = ⊤ := by
    refine Opens.ext (Set.eq_univ_of_forall fun w => ?_)
    rw [show w = z from Subsingleton.elim w z]
    exact hzW
  subst hW
  rw [Subsingleton.elim iU (𝟙 _), Subsingleton.elim iV (𝟙 _), op_id,
    CategoryTheory.Functor.map_id] at h
  exact h

/-- **Reading a global function on the generic fibre as a rational function loses nothing.** The
comparison is the germ at the single point of the generic fibre followed by isomorphisms of local
rings, and a section of a one-point scheme is determined by its germ. -/
theorem injective_genericFibreToFunctionField {X V : Scheme.{u}} [IsIntegral X] [IsIntegral V]
    (g : V ⟶ X) [Etale g] : Function.Injective (genericFibreToFunctionField g) := by
  have := subsingleton_pullback_genericPointInclusion g
  have hiso : IsIso ((pullback.fst g (genericPointInclusion X)).stalkMap
      (genericFibrePoint g)) :=
    isIso_stalkMap_pullback_fst_genericPointInclusion X g (genericFibrePoint g)
  have hψ : Function.Injective
      (inv ((pullback.fst g (genericPointInclusion X)).stalkMap (genericFibrePoint g)) ≫
        (V.presheaf.stalkCongr (Inseparable.of_eq (fst_base_genericFibrePoint g))).hom) :=
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  intro s t hst
  refine injective_germ_top_of_subsingleton (genericFibrePoint g) (hψ ?_)
  exact hst

end Fibre

section Middle

open _root_.Stacks.AlgebraicGeometry.UnitsNormalProper in
/-- **A function on the generic fibre with no zeros and no poles is the restriction of an
invertible global function.** This is algebraic Hartogs on a normal scheme, applied to the
rational function and to its inverse; the two global sections produced are inverse to one
another because a section of an integral scheme is determined by its germ at the generic
point. -/
theorem exists_units_restrict_eq_of_forall_ord_eq_zero {X V : Scheme.{u}} [IsIntegral X]
    [IsIntegral V] [IsLocallyNoetherian V] [AlgebraicGeometry.IsNormal V]
    (g : V ⟶ X) [Etale g]
    (a : (Γ(pullback g (genericPointInclusion X), ⊤))ˣ)
    (h0 : ∀ y : V, coheight y = 1 →
      Scheme.ord (genericFibreToFunctionField g
        (a : Γ(pullback g (genericPointInclusion X), ⊤))) y = 0) :
    ∃ b : (Γ(V, ⊤))ˣ,
      Units.map (pullback.fst g (genericPointInclusion X)).appTop.hom.toMonoidHom b = a := by
  set w := genericFibreToFunctionField g (a : Γ(pullback g (genericPointInclusion X), ⊤))
    with hw
  set w' := genericFibreToFunctionField g ((a⁻¹ : (Γ(pullback g (genericPointInclusion X),
    ⊤))ˣ) : Γ(pullback g (genericPointInclusion X), ⊤)) with hw'
  have hmul : w * w' = 1 := by
    rw [hw, hw', ← map_mul]
    simp
  have hwne : w ≠ 0 := fun h => by simp [h] at hmul
  have hw'ne : w' ≠ 0 := fun h => by simp [h] at hmul
  have h0' : ∀ y : V, coheight y = 1 → Scheme.ord w' y = 0 := by
    intro y hy
    have h := Scheme.ord_mul (X := V) (x := y) hwne hw'ne
    rw [hmul, Scheme.ord_one, h0 y hy] at h
    omega
  obtain ⟨c, hc⟩ := exists_globalSection_of_forall_ord_eq_zero (X := V) hwne h0
  obtain ⟨c', hc'⟩ := exists_globalSection_of_forall_ord_eq_zero (X := V) hw'ne h0'
  have hcc : c * c' = 1 := by
    refine germ_injective_of_isIntegral (X := V) (U := ⊤) (genericPoint V) trivial ?_
    rw [map_mul, hc, hc', hmul, map_one]
  refine ⟨⟨c, c', hcc, by rw [mul_comm]; exact hcc⟩, Units.ext ?_⟩
  have hres : genericFibreToFunctionField g
      ((pullback.fst g (genericPointInclusion X)).appTop c) =
      V.presheaf.germ ⊤ (genericPoint V) trivial c :=
    congrArg (fun φ => (CommRingCat.Hom.hom φ) c) (appTop_genericFibreToFunctionField g)
  refine injective_genericFibreToFunctionField g ?_
  exact hres.trans (hc.trans hw)

/-- **Exactness in the middle of the fundamental exact sequence of Stacks 03RI, read on sections
over an irreducible étale neighbourhood `U` of a smooth curve `X`.** A section of
`j_* 𝐆_{m,η}` over `U` killed by the divisor map is the restriction of an invertible global
function on `U`.

Every point of `U` of codimension one lies over a closed point of `X`, so the vanishing of the
divisor map at the closed points of `X` is the vanishing of all orders of vanishing on `U`, and
algebraic Hartogs then produces the global function. -/
theorem exists_restrict_eq_of_genericFibreDivisorSections_eq_zero
    {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsCurve k fX]
    (U : X.Etale) [IsIntegral U.left] [IsLocallyNoetherian U.left] [NoetherianSpace U.left]
    [AlgebraicGeometry.IsNormal U.left]
    (a : (Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)
    (h : genericFibreDivisorSections.{u, v} U (Additive.ofMul a) = 0) :
    ∃ b : (Γ(U.left, ⊤))ˣ,
      Units.map (pullback.fst U.hom (genericPointInclusion X)).appTop.hom.toMonoidHom b = a := by
  have hint : IsIntegral ((𝟭 Scheme).obj U.left) := inferInstanceAs (IsIntegral U.left)
  have hln : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) :=
    inferInstanceAs (IsLocallyNoetherian U.left)
  have hnorm : AlgebraicGeometry.IsNormal ((𝟭 Scheme).obj U.left) :=
    inferInstanceAs (AlgebraicGeometry.IsNormal U.left)
  have hlqf : LocallyQuasiFinite U.hom := (AlgebraicGeometry.locallyQuasiFinite_of_etale U.hom).2
  refine exists_units_restrict_eq_of_forall_ord_eq_zero (X := X) U.hom a fun y hy => ?_
  have hyg : y ≠ genericPoint U.left := by
    intro hyg
    rw [hyg, coheight_genericPoint_eq_zero] at hy
    simp at hy
  have hxg : U.hom y ≠ genericPoint X := fun hc =>
    hyg (eq_genericPoint_of_base_eq_genericPoint U.hom hc)
  have hxmem : U.hom y ∈ closedPoints X :=
    isClosed_singleton_of_isCurve fX hxg
  have hx0 : integerSkyscraperDivisor.{u, v} U (U.hom y) (Additive.ofMul a) = 0 := by
    have hev := congrArg (fun d : DirectSum ↥(closedPoints X) _ => d ⟨U.hom y, hxmem⟩) h
    simpa [genericFibreDivisorSections_apply] using hev
  have hinj : Function.Injective
      (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X (U.hom y) U).inv :=
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  have hres0 : residueFibreOrd.{u, v} U (U.hom y) (Additive.ofMul a) = 0 := by
    refine hinj ?_
    simpa [integerSkyscraperDivisor] using hx0
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := U.hom)
    (g := X.fromSpecResidueField (U.hom y)) y
    (Classical.arbitrary ↥(Spec (X.residueField (U.hom y))))
    (Scheme.fromSpecResidueField_apply _ _).symm
  have hord : etaleGenericFibreOrd U y (Additive.ofMul a) = 0 := by
    have hev : (residueFibreOrd.{u, v} U (U.hom y) (Additive.ofMul a)) z = 0 := by
      rw [hres0]; rfl
    have h2 := residueFibreOrd_apply.{u, v} U (U.hom y) (Additive.ofMul a) z
    rw [hz] at h2
    exact congrArg ULift.down (h2.symm.trans hev)
  exact (genericFibreOrd_apply (X := X) U.hom y (Additive.ofMul a)).symm.trans hord

end Middle

end Stacks.EtaleCohomology

end
