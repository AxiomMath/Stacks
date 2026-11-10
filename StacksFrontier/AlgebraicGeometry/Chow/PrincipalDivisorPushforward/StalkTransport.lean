module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm

/-!
# Transporting stalks, function fields and orders of vanishing

This file proves transport lemmas for stalks, function fields and orders of vanishing.

* The identification of a stalk at a point with the stalk at an equal point is compatible with
  germs, residue fields and the stalk map of a morphism, and Mathlib's
  `TopCat.Presheaf.stalkCongr` agrees with the `eqToHom` of the equality
  (`Stacks.Chow.eqToHom_stalkCongr`).
* A dominant morphism of integral schemes that is an isomorphism on local rings, an open immersion
  for instance, identifies the function fields and, where it preserves codimension, the orders of
  vanishing. The residue degree of a morphism is unchanged by precomposition or postcomposition
  with an open immersion.
* `Ring.ord`, `Ring.ordFrac` and `ordInt` are invariant under ring isomorphisms.

## Main results

* `Stacks.Chow.dominantFunctionFieldMap_comp` — the function-field map of a dominant morphism of
  integral schemes is functorial.
* `Stacks.Chow.functionFieldEquiv_of_isIso_stalkMap`,
  `Stacks.Chow.functionFieldEquiv_openImmersion` — a dominant morphism of integral schemes that is
  an isomorphism on the local ring at the generic point, an open immersion in particular,
  identifies the function fields.
* `Stacks.Chow.ord_dominantFunctionFieldMap_of_isIso_stalkMap`,
  `Stacks.Chow.ord_dominantFunctionFieldMap_of_isOpenImmersion` — the order of vanishing depends
  only on the local ring, so it is in particular local.
* `Stacks.Chow.residueDegree_comp_of_bijective_residueFieldMap`,
  `Stacks.Chow.residueDegree_of_bijective_residueFieldMap_comp`,
  `Stacks.Chow.residueDegree_comp_isOpenImmersion`,
  `Stacks.Chow.residueDegree_isOpenImmersion_comp`,
  `Stacks.Chow.residueDegree_morphismRestrict` — the residue degree does not see a factor that is
  bijective on residue fields, so it is in particular local.
* `Stacks.Chow.ordFrac_congr` — `Ring.ordFrac` is invariant under a compatible pair of ring
  isomorphisms, hence so is `ordInt` (`Stacks.Chow.ordInt_congr`).
* `Stacks.Chow.ord_eq_ordInt` — the order of vanishing of a scheme at a point of codimension one
  is the `ordInt` of its stalk.

## References

* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Stalks at equal points -/

/-- The `eqToHom` of an equality of stalks is the inverse of Mathlib's stalk congruence. -/
theorem eqToHom_stalkCongr {X : TopCat} (F : TopCat.Presheaf CommRingCat X) {x y : X}
    (h : x = y) :
    eqToHom (congrArg F.stalk h) = (F.stalkCongr (Inseparable.of_eq h.symm)).inv := by
  cases h
  simp

/-- The inverse of the stalk congruence of an equality is the forward map of the reversed
equality. -/
theorem stalkCongr_inv_hom {T : TopCat.{u}} (F : T.Presheaf CommRingCat.{u}) {x y : T}
    (h : x = y) :
    (F.stalkCongr (Inseparable.of_eq h)).inv = (F.stalkCongr (Inseparable.of_eq h.symm)).hom := by
  cases h
  rfl

/-- The stalk congruence of an equality of points of a scheme is the `eqToHom` of that
equality. -/
theorem stalkCongr_eq_eqToHom {X : Scheme.{u}} {x y : X} (h : x = y) :
    (X.presheaf.stalkCongr (.of_eq h)).hom = eqToHom (congrArg X.presheaf.stalk h) := by
  cases h
  rw [TopCat.Presheaf.stalkCongr_hom]
  simp

/-- Transporting the stalk map of a morphism along an equality of its target point is
precomposition with the stalk congruence. -/
theorem stalkMap_cast_target {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) {y : Y} (h : f.base x = y) :
    h ▸ f.stalkMap x =
      (Y.presheaf.stalkCongr (Inseparable.of_eq h.symm)).hom ≫ f.stalkMap x := by
  cases h
  simp

/-- Transporting the stalk map of a morphism along an equality of its target point is
precomposition with the `eqToHom` of that equality. -/
theorem stalkMap_eqToHom_eq_cast {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (h : f.base x = y) :
    eqToHom (congrArg Y.presheaf.stalk h.symm) ≫ f.stalkMap x = h ▸ f.stalkMap x := by
  cases h
  rfl

/-- Transporting a stalk map along an equality of its target point commutes with taking germs. -/
theorem stalkMap_germ_transport {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (V : Y.Opens) {z : Y}
    (h : f.base x = z) (hz : z ∈ V) (a : Γ(Y, V)) :
    (h ▸ f.stalkMap x) (Y.presheaf.germ V z hz a) =
      f.stalkMap x (Y.presheaf.germ V (f.base x) (h.symm ▸ hz) a) := by
  cases h
  rfl

/-- The identification of residue fields at equal points is compatible with the residue maps. -/
theorem residueField_eqToHom_comp_residue (Y : Scheme.{u}) {x y : Y} (h : x = y) :
    (eqToHom (congrArg Y.residueField h)).hom.comp (Y.residue x).hom =
      (Y.residue y).hom.comp (eqToHom (congrArg Y.presheaf.stalk h)).hom := by
  cases h
  simp

/-- The identification of stalks at equal points is compatible with germs. -/
theorem stalk_eqToHom_comp_germ (Y : Scheme.{u}) {x y : Y} (h : x = y) (U : Y.Opens)
    (hx : x ∈ U) :
    (eqToHom (congrArg Y.presheaf.stalk h)).hom.comp (Y.presheaf.germ U x hx).hom =
      (Y.presheaf.germ U y (h ▸ hx)).hom := by
  cases h
  simp

/-! ### Functoriality of the function-field map -/

/-- **Stacks 02JU.** The extension of function fields induced by a dominant morphism of integral
schemes is contravariantly functorial. -/
theorem dominantFunctionFieldMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z] [IsDominant f] [IsDominant g] :
    dominantFunctionFieldMap (f ≫ g) =
      (dominantFunctionFieldMap f).comp (dominantFunctionFieldMap g) := by
  have hf : f.base (genericPoint X) = genericPoint Y :=
    ((tfae_isDominant_of_isIntegral f).out 1 2).mp (inferInstance : IsDominant f)
  have hg : g.base (genericPoint Y) = genericPoint Z :=
    ((tfae_isDominant_of_isIntegral g).out 1 2).mp (inferInstance : IsDominant g)
  have hfg : (f ≫ g).base (genericPoint X) = genericPoint Z := (congrArg g.base hf).trans hg
  have hcast :
      eqToHom (congrArg Z.presheaf.stalk hfg.symm) ≫
          eqToHom (congrArg Z.presheaf.stalk (congrArg g.base hf)) =
        eqToHom (congrArg Z.presheaf.stalk hg.symm) :=
    eqToHom_trans _ _
  set φf : Y.functionField →+* X.functionField :=
    (eqToHom (congrArg Y.presheaf.stalk hf.symm) ≫ f.stalkMap (genericPoint X)).hom with hφf
  set φg : Z.functionField →+* Y.functionField :=
    (eqToHom (congrArg Z.presheaf.stalk hg.symm) ≫ g.stalkMap (genericPoint Y)).hom with hφg
  set φfg : Z.functionField →+* X.functionField :=
    (eqToHom (congrArg Z.presheaf.stalk hfg.symm) ≫ (f ≫ g).stalkMap (genericPoint X)).hom
    with hφfg
  have hNat := g.stalkMap_congr_point (f.base (genericPoint X)) (genericPoint Y) hf
  rw [stalkCongr_eq_eqToHom hf, stalkCongr_eq_eqToHom (congrArg g.base hf)] at hNat
  have hNat' : g.stalkMap (f.base (genericPoint X)) =
      eqToHom (congrArg Z.presheaf.stalk (congrArg g.base hf)) ≫
        g.stalkMap (genericPoint Y) ≫ eqToHom (congrArg Y.presheaf.stalk hf.symm) := by
    calc g.stalkMap (f.base (genericPoint X))
        = g.stalkMap (f.base (genericPoint X)) ≫
            (eqToHom (congrArg Y.presheaf.stalk hf) ≫
              eqToHom (congrArg Y.presheaf.stalk hf.symm)) := by simp
      _ = (eqToHom (congrArg Z.presheaf.stalk (congrArg g.base hf)) ≫
            g.stalkMap (genericPoint Y)) ≫ eqToHom (congrArg Y.presheaf.stalk hf.symm) := by
          rw [← Category.assoc, hNat]
  have hφ : φfg = φf.comp φg := by
    rw [hφfg, hφf, hφg]
    apply congrArg CommRingCat.Hom.hom
    calc eqToHom (congrArg Z.presheaf.stalk hfg.symm) ≫ (f ≫ g).stalkMap (genericPoint X)
        = eqToHom (congrArg Z.presheaf.stalk hfg.symm) ≫
            (g.stalkMap (f.base (genericPoint X)) ≫ f.stalkMap (genericPoint X)) :=
          congrArg (fun k ↦ eqToHom (congrArg Z.presheaf.stalk hfg.symm) ≫ k)
            (Scheme.Hom.stalkMap_comp f g (genericPoint X))
      _ = (eqToHom (congrArg Z.presheaf.stalk hg.symm) ≫ g.stalkMap (genericPoint Y)) ≫
            (eqToHom (congrArg Y.presheaf.stalk hf.symm) ≫ f.stalkMap (genericPoint X)) := by
          rw [hNat']
          calc _ = (eqToHom (congrArg Z.presheaf.stalk hfg.symm) ≫
                    eqToHom (congrArg Z.presheaf.stalk (congrArg g.base hf))) ≫
                  g.stalkMap (genericPoint Y) ≫
                    eqToHom (congrArg Y.presheaf.stalk hf.symm) ≫
                      f.stalkMap (genericPoint X) := by cat_disch
            _ = eqToHom (congrArg Z.presheaf.stalk hg.symm) ≫ g.stalkMap (genericPoint Y) ≫
                  eqToHom (congrArg Y.presheaf.stalk hf.symm) ≫
                    f.stalkMap (genericPoint X) := by rw [hcast]
            _ = (eqToHom (congrArg Z.presheaf.stalk hg.symm) ≫ g.stalkMap (genericPoint Y)) ≫
                  (eqToHom (congrArg Y.presheaf.stalk hf.symm) ≫
                    f.stalkMap (genericPoint X)) := by simp only [Category.assoc]
  have hcastMapF (a : Y.functionField) : dominantFunctionFieldMap f a = φf a := by
    rw [hφf]
    change (hf ▸ f.stalkMap (genericPoint X)).hom a = _
    rw [stalkMap_cast_target f (genericPoint X) hf, eqToHom_stalkCongr Y.presheaf hf.symm,
      stalkCongr_inv_hom Y.presheaf hf]
  have hcastMapG (a : Z.functionField) : dominantFunctionFieldMap g a = φg a := by
    rw [hφg]
    change (hg ▸ g.stalkMap (genericPoint Y)).hom a = _
    rw [stalkMap_cast_target g (genericPoint Y) hg, eqToHom_stalkCongr Z.presheaf hg.symm,
      stalkCongr_inv_hom Z.presheaf hg]
  have hcastMapFG (a : Z.functionField) : dominantFunctionFieldMap (f ≫ g) a = φfg a := by
    rw [hφfg]
    change (hfg ▸ (f ≫ g).stalkMap (genericPoint X)).hom a = _
    rw [stalkMap_cast_target (f ≫ g) (genericPoint X) hfg, stalkCongr_eq_eqToHom hfg.symm]
  ext a
  calc dominantFunctionFieldMap (f ≫ g) a = φfg a := hcastMapFG a
    _ = (φf.comp φg) a := DFunLike.congr_fun hφ a
    _ = (dominantFunctionFieldMap f).comp (dominantFunctionFieldMap g) a := by
        change φf (φg a) = dominantFunctionFieldMap f (dominantFunctionFieldMap g a)
        rw [← hcastMapG a, ← hcastMapF (dominantFunctionFieldMap g a)]

/-! ### Morphisms that are isomorphisms on local rings -/

/-- A dominant morphism of integral schemes that is an isomorphism on local rings at the generic
point induces an isomorphism of function fields: the function-field map is the stalk map at the
generic point, transported along the identification of its image with the generic point of the
target. -/
def functionFieldEquiv_of_isIso_stalkMap {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant i] (hiso : IsIso (i.stalkMap (genericPoint Y))) :
    X.functionField ≃+* Y.functionField := by
  have _ := hiso
  have hη : i.base (genericPoint Y) = genericPoint X :=
    ((tfae_isDominant_of_isIntegral i).out 1 2).mp (inferInstance : IsDominant i)
  refine RingEquiv.ofBijective (dominantFunctionFieldMap i) ⟨RingHom.injective _, fun b ↦ ?_⟩
  obtain ⟨a, ha⟩ := (asIso (i.stalkMap (genericPoint Y))).commRingCatIsoToRingEquiv.surjective b
  change (i.stalkMap (genericPoint Y)).hom a = b at ha
  refine ⟨(eqToHom (congrArg X.presheaf.stalk hη)).hom a, ?_⟩
  calc dominantFunctionFieldMap i ((eqToHom (congrArg X.presheaf.stalk hη)).hom a)
      = (i.stalkMap (genericPoint Y)).hom a := by
        change (hη ▸ i.stalkMap (genericPoint Y)).hom
          ((eqToHom (congrArg X.presheaf.stalk hη)).hom a) = _
        rw [stalkMap_cast_target i (genericPoint Y) hη, eqToHom_stalkCongr X.presheaf hη]
        have hcancel := congrArg (i.stalkMap (genericPoint Y)).hom
          (congrArg (fun m : CommRingCat.Hom _ _ ↦ m.hom a)
            (Iso.inv_hom_id (X.presheaf.stalkCongr (Inseparable.of_eq hη.symm))))
        simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
          CommRingCat.hom_id, RingHom.id_apply] using hcancel
    _ = b := ha

/-! ### Open immersions -/

/-- A dominant open immersion into an integral scheme induces an isomorphism of function
fields. -/
def functionFieldEquiv_openImmersion {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
    [IsIntegral X] [IsIntegral Y] [IsDominant i] : X.functionField ≃+* Y.functionField :=
  functionFieldEquiv_of_isIso_stalkMap i inferInstance

/-- The residue degree of `f ≫ j` at `x` is the residue degree of `f` at `x` when `j` is
bijective on the residue fields at `f x`. -/
theorem residueDegree_comp_of_bijective_residueFieldMap {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (j : Y ⟶ Z) (x : X) (hj : Function.Bijective (j.residueFieldMap (f.base x)).hom) :
    (f ≫ j).residueDegree x = f.residueDegree x := by
  rw [Scheme.Hom.residueDegree, Scheme.Hom.residueDegree]
  set e₁ : Z.residueField (j.base (f.base x)) ≃+* Y.residueField (f.base x) :=
    RingEquiv.ofBijective (j.residueFieldMap (f.base x)).hom hj
  let _ : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let _ : Algebra (Z.residueField (j.base (f.base x))) (X.residueField x) :=
    ((f ≫ j).residueFieldMap x).hom.toAlgebra
  refine (Algebra.finrank_eq_of_equiv_equiv e₁.symm (RingEquiv.refl (X.residueField x)) ?_).symm
  have hcomp := congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f j x)
  ext a
  change ((f ≫ j).residueFieldMap x).hom (e₁.symm a) = (f.residueFieldMap x).hom a
  rw [hcomp]
  change (f.residueFieldMap x).hom ((j.residueFieldMap (f.base x)).hom (e₁.symm a)) =
    (f.residueFieldMap x).hom a
  congr 1
  exact e₁.apply_symm_apply a

/-- The residue degree of a morphism is unchanged by postcomposition with an open immersion. -/
theorem residueDegree_comp_isOpenImmersion {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Y ⟶ Z)
    [IsOpenImmersion j] (x : X) : (f ≫ j).residueDegree x = f.residueDegree x :=
  residueDegree_comp_of_bijective_residueFieldMap f j x (ConcreteCategory.bijective_of_isIso _)

/-- The residue degree of `i ≫ f` at `x` is the residue degree of `f` at `i x` when `i` is
bijective on the residue fields at `x`. -/
theorem residueDegree_of_bijective_residueFieldMap_comp {X' X Y : Scheme.{u}} (i : X' ⟶ X)
    (f : X ⟶ Y) (x : X') (hi : Function.Bijective (i.residueFieldMap x).hom) :
    (i ≫ f).residueDegree x = f.residueDegree (i.base x) := by
  rw [Scheme.Hom.residueDegree, Scheme.Hom.residueDegree]
  set e : X.residueField (i.base x) ≃+* X'.residueField x :=
    RingEquiv.ofBijective (i.residueFieldMap x).hom hi
  let _ : Algebra (Y.residueField (f.base (i.base x))) (X.residueField (i.base x)) :=
    (f.residueFieldMap (i.base x)).hom.toAlgebra
  let _ : Algebra (Y.residueField (f.base (i.base x))) (X'.residueField x) :=
    ((i ≫ f).residueFieldMap x).hom.toAlgebra
  refine (Algebra.finrank_eq_of_equiv_equiv
    (RingEquiv.refl (Y.residueField (f.base (i.base x)))) e ?_).symm
  have hcomp := congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp i f x)
  ext a
  change ((i ≫ f).residueFieldMap x).hom a = e ((f.residueFieldMap (i.base x)).hom a)
  rw [hcomp]
  rfl

/-- The residue degree of a morphism at a point of an open subscheme is the residue degree of the
restricted morphism. -/
theorem residueDegree_isOpenImmersion_comp {X' X Y : Scheme.{u}} (i : X' ⟶ X) [IsOpenImmersion i]
    (f : X ⟶ Y) (x : X') : (i ≫ f).residueDegree x = f.residueDegree (i.base x) :=
  residueDegree_of_bijective_residueFieldMap_comp i f x (ConcreteCategory.bijective_of_isIso _)

/-- The residue degree of the restriction of a morphism over an open subscheme of the target is
the residue degree of the morphism itself. -/
theorem residueDegree_morphismRestrict {X Y : Scheme.{u}} (p : X ⟶ Y) (V : Y.Opens)
    (x : (p ⁻¹ᵁ V).toScheme) :
    (p ∣_ V).residueDegree x = p.residueDegree ((p ⁻¹ᵁ V).ι.base x) := by
  calc (p ∣_ V).residueDegree x
      = ((p ∣_ V) ≫ V.ι).residueDegree x :=
        (residueDegree_comp_isOpenImmersion (p ∣_ V) V.ι x).symm
    _ = ((p ⁻¹ᵁ V).ι ≫ p).residueDegree x := by rw [morphismRestrict_ι]
    _ = p.residueDegree ((p ⁻¹ᵁ V).ι.base x) :=
        residueDegree_isOpenImmersion_comp (p ⁻¹ᵁ V).ι p x

/-! ### Invariance of the order of vanishing -/

/-- `Ring.ord` is invariant under a ring isomorphism of domains. -/
theorem ord_congr {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (e : R ≃+* S) (x : R) : Ring.ord S (e x) = Ring.ord R x := by
  set E : Ideal S ≃o Ideal R := Ideal.relIsoOfBijective (e : R →+* S) e.bijective
  rw [Ring.ord, Ring.ord, Module.length_quotient, Module.length_quotient]
  have he : E (Ideal.span {e x}) = Ideal.span {x} := by
    ext a
    change e a ∈ Ideal.span {e x} ↔ a ∈ Ideal.span {x}
    rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    refine ⟨fun ⟨b, hb⟩ ↦ ⟨e.symm b, e.injective (by simpa using hb)⟩, ?_⟩
    rintro ⟨b, rfl⟩
    exact ⟨e b, map_mul e x b⟩
  rw [← he]
  exact (Order.coheight_orderIso E _).symm

/-- `Ring.ordFrac` is invariant under a ring isomorphism of one-dimensional Noetherian domains
compatible with an isomorphism of their fraction fields. -/
theorem ordFrac_congr {R S K L : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [CommRing S] [IsDomain S] [IsNoetherianRing S] [Ring.KrullDimLE 1 S]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra S L] [IsFractionRing S L]
    (e : R ≃+* S) (E : K ≃+* L) (h : ∀ r : R, E (algebraMap R K r) = algebraMap S L (e r))
    (f : K) : Ring.ordFrac S (E f) = Ring.ordFrac R f := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R f
  rw [map_div₀]
  simp only [h]
  have hb' : e b ∈ nonZeroDivisors S := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact fun hzero ↦ (mem_nonZeroDivisors_iff_ne_zero.mp hb) (e.injective (by simpa using hzero))
  by_cases ha : a = 0
  · simp [ha]
  have ha' : e a ∈ nonZeroDivisors S := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact fun hzero ↦ ha (e.injective (by simpa using hzero))
  rw [← IsFractionRing.mk'_mk_eq_div hb, ← IsFractionRing.mk'_mk_eq_div hb',
    Ring.ordFrac_eq_div S ⟨e a, ha'⟩ ⟨e b, hb'⟩,
    Ring.ordFrac_eq_div R ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩ ⟨b, hb⟩,
    Ring.ordMonoidWithZeroHom_eq_ord ha',
    Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_iff_ne_zero.mpr ha),
    Ring.ordMonoidWithZeroHom_eq_ord hb', Ring.ordMonoidWithZeroHom_eq_ord hb,
    ord_congr e a, ord_congr e b]

/-- `ordInt` is invariant under a ring isomorphism of one-dimensional Noetherian domains
compatible with an isomorphism of their fraction fields. -/
theorem ordInt_congr {R S K L : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [CommRing S] [IsDomain S] [IsNoetherianRing S] [Ring.KrullDimLE 1 S]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra S L] [IsFractionRing S L]
    (e : R ≃+* S) (E : K ≃+* L) (h : ∀ r : R, E (algebraMap R K r) = algebraMap S L (e r))
    (f : K) (hf : f ≠ 0) (hEf : E f ≠ 0) : ordInt S (E f) hEf = ordInt R f hf := by
  simp only [ordInt, ordFrac_congr e E h f]

/-- The order of vanishing of a locally Noetherian integral scheme at a point of codimension one
is the `ordInt` of the stalk at that point. -/
theorem ord_eq_ordInt {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (x : X)
    [Ring.KrullDimLE 1 (X.presheaf.stalk x)] (hx : coheight x = 1) (z : X.functionField)
    (hz : z ≠ 0) :
    X.ord z x = ordInt (X.presheaf.stalk x) z hz := by
  rw [Scheme.ord_eq_unzero_ordHom hx hz]
  rfl

/-- If a dominant morphism of integral schemes is an isomorphism on the local rings at the
generic point and at `y`, and does not change the codimension of `y`, then the order of vanishing
at `y` of the pullback of a rational function is its order of vanishing at the image of `y`. -/
theorem ord_dominantFunctionFieldMap_of_isIso_stalkMap {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant i] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hgeniso : IsIso (i.stalkMap (genericPoint Y))) (y : Y) (hyiso : IsIso (i.stalkMap y))
    (hco : coheight (i.base y) = coheight y) (f : X.functionField) :
    Y.ord (dominantFunctionFieldMap i f) y = X.ord f (i.base y) := by
  have _ := hyiso
  have hη : i.base (genericPoint Y) = genericPoint X :=
    ((tfae_isDominant_of_isIntegral i).out 1 2).mp (inferInstance : IsDominant i)
  set E := functionFieldEquiv_of_isIso_stalkMap i hgeniso
  change Y.ord (E f) y = X.ord f (i.base y)
  set e : X.presheaf.stalk (i.base y) ≃+* Y.presheaf.stalk y :=
    (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv
  have hgen := (genericPoint_spec Y).specializes (Set.mem_univ y)
  have hgenX : genericPoint X ⤳ i.base y := by
    rw [← hη]
    exact hgen.map i.continuous
  have hfieldMap (a : X.presheaf.stalk (genericPoint X)) :
      dominantFunctionFieldMap i a =
        (i.stalkMap (genericPoint Y)).hom
          ((eqToHom (congrArg X.presheaf.stalk hη.symm)).hom a) := by
    change (hη ▸ i.stalkMap (genericPoint Y)).hom a = _
    rw [stalkMap_cast_target i (genericPoint Y) hη, eqToHom_stalkCongr X.presheaf hη.symm,
      stalkCongr_inv_hom X.presheaf hη]
    rfl
  have hfield (a : X.presheaf.stalk (i.base y)) :
      E (algebraMap (X.presheaf.stalk (i.base y)) X.functionField a) =
        algebraMap (Y.presheaf.stalk y) Y.functionField (e a) := by
    change dominantFunctionFieldMap i ((X.presheaf.stalkSpecializes hgenX).hom a) =
      (Y.presheaf.stalkSpecializes hgen).hom ((i.stalkMap y).hom a)
    have hmap := i.base.hom.map_specializes hgen
    have hstalkHom :
        X.presheaf.stalkSpecializes hgenX ≫ eqToHom (congrArg X.presheaf.stalk hη.symm) =
          X.presheaf.stalkSpecializes hmap := by
      rw [eqToHom_stalkCongr X.presheaf hη.symm, TopCat.Presheaf.stalkCongr_inv,
        TopCat.Presheaf.stalkSpecializes_comp X.presheaf (Inseparable.of_eq hη).le hgenX]
    have hc := congrArg (fun g : X.presheaf.stalk (i.base y) ⟶ Y.presheaf.stalk (genericPoint Y) ↦
      g a) (Scheme.Hom.stalkSpecializes_stalkMap i (genericPoint Y) y hgen)
    calc _ = (i.stalkMap (genericPoint Y)).hom
            ((eqToHom (congrArg X.presheaf.stalk hη.symm)).hom
              ((X.presheaf.stalkSpecializes hgenX).hom a)) := hfieldMap _
      _ = (i.stalkMap (genericPoint Y)).hom ((X.presheaf.stalkSpecializes hmap).hom a) :=
          congrArg _ (congrArg (fun g ↦ g a) hstalkHom)
      _ = (Y.presheaf.stalkSpecializes hgen).hom ((i.stalkMap y).hom a) := by
          simpa only [CommRingCat.comp_apply] using hc
  by_cases hy : coheight y = 1
  · have hiy : coheight (i.base y) = 1 := hco.trans hy
    let _ : Ring.KrullDimLE 1 (X.presheaf.stalk (i.base y)) := krullDimLE_of_coheight_le hiy.le
    let _ : Ring.KrullDimLE 1 (Y.presheaf.stalk y) := krullDimLE_of_coheight_le hy.le
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hy, Scheme.ord_eq_ordHom_of_coheight_eq_one hiy]
    exact congrArg (fun z ↦ Multiplicative.toAdd (WithZero.unzeroD 1 z))
      (ordFrac_congr e E hfield f)
  · have hiy : coheight (i.base y) ≠ 1 := by rwa [hco]
    simp [hy, hiy]

/-- The order of vanishing of a rational function on an integral scheme is unchanged by passing to
a nonempty open subscheme. -/
theorem ord_dominantFunctionFieldMap_of_isOpenImmersion {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsOpenImmersion i] [IsIntegral X] [IsIntegral Y] [IsDominant i] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X.functionField) (y : Y) :
    Y.ord (dominantFunctionFieldMap i f) y = X.ord f (i.base y) :=
  ord_dominantFunctionFieldMap_of_isIso_stalkMap i inferInstance y inferInstance
    (coheight_eq_of_isOpenImmersion (f := i)) f

/-! ### Germs and the function field -/

/-- For a dominant morphism of integral schemes, the square relating the map on sections over
`U ≤ f ⁻¹ V` to the map on function fields commutes. -/
theorem appLE_germToFunctionField_commutes {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X]
    [IsIntegral Y] [IsDominant f] (V : Y.Opens) [Nonempty V] (U : X.Opens) [Nonempty U]
    (hUV : U ≤ f ⁻¹ᵁ V) :
    (X.germToFunctionField U).hom.comp (f.appLE V U hUV).hom =
      (dominantFunctionFieldMap f).comp (Y.germToFunctionField V).hom := by
  have hη : f.base (genericPoint X) = genericPoint Y :=
    ((tfae_isDominant_of_isIntegral f).out 1 2).mp (inferInstance : IsDominant f)
  have hηV : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using (‹Nonempty V› : _))
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using (‹Nonempty U› : _))
  ext a
  simp only [RingHom.comp_apply]
  dsimp [Scheme.germToFunctionField, dominantFunctionFieldMap]
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    X.presheaf.germ_res_apply]
  rw [← Scheme.Hom.germ_stalkMap_apply (f := f) V (genericPoint X) (hη.symm ▸ hηV)]
  exact (stalkMap_germ_transport f (genericPoint X) V hη hηV a).symm

end Stacks.Chow

end
