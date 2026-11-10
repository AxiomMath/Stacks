module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreOrdBaseChange

/-!
# Orders of vanishing and divisors along a ramified morphism

Let `π : X ⟶ Y` be a flat dominant morphism of integral schemes. At a point `x` of `X` over
`y = π x` the local ring `𝒪_{X,x}` is a flat `𝒪_{Y,y}`-algebra, and the colength

`e_x = length_{𝒪_{X,x}} (𝒪_{X,x} / 𝔪_y 𝒪_{X,x})`

is the local multiplicity of `π` at `x`: it is `1` exactly when `𝔪_y` generates `𝔪_x`, and for
an extension of discrete valuation rings it is the exponent in `𝔪_y 𝒪_{X,x} = 𝔪_x^{e_x}`. The
order of vanishing of a rational function pulled back along `π` is then

`ord_x(π^# g) = e_x · ord_y(g)`,

with no hypothesis on `π` beyond flatness, dominance and the equality of codimensions at `x` and
`y`. This is the general form of `Stacks.Chow.ord_dominantFunctionFieldMap_of_flat`, which asks
`𝔪_y 𝒪_{X,x} = 𝔪_x`, that is `e_x = 1`.

Pushed to the generic fibres of étale schemes over two bases, the same identity is the pointwise
content of the third square of a morphism of divisor sequences along a ramified cover. The third
component itself, the weighted map

`⨁_{y ∈ Y_0} i_{y,*} 𝐙 ⟶ π_* (⨁_{x ∈ X_0} i_{x,*} 𝐙)`,

sends the summand at a closed point `y` to the sum over the closed points `x` above `y` of `e_x`
times `Stacks.EtaleCohomology.integerSkyscraperDirectImageMap`. The finite set of points above
`y` is part of the input, as the multiplicity-one map
`Stacks.EtaleCohomology.closedPointDivisorDirectImageMap` takes a choice of one point above each
closed point as its input.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.ramificationLength`: the multiplicity `e_x` above.
* `Stacks.EtaleCohomology.weightedIntegerSkyscraperDirectImageMap`: the contribution
  `i_{y,*} 𝐙 ⟶ π_* (⨁_x i_{x,*} 𝐙)` of a single closed point `x` above `y`, with a weight.
* `Stacks.EtaleCohomology.ramifiedClosedPointDivisorDirectImageMap`: **the ramification-weighted
  third component of the morphism of divisor sequences.**

## Main results

* `AlgebraicGeometry.Scheme.Hom.ramificationLength_eq_one_of_map_maximalIdeal_eq`: the
  multiplicity is one where the maximal ideal generates the maximal ideal.
* `AlgebraicGeometry.Scheme.Hom.ramificationLength_of_comp_eq`: the multiplicity is unchanged by
  restriction to opens.
* `Stacks.Chow.ord_dominantFunctionFieldMap_eq_ramificationLength_mul`: **the order-of-vanishing
  identity `ord_x(π^# g) = e_x · ord_y(g)`.**
* `Stacks.EtaleCohomology.genericFibreOrd_appTop_eq_ramificationLength_mul_of_square` and
  `Stacks.EtaleCohomology.genericFibreOrdOfPoint_appTop_eq_ramificationLength_mul_of_square`: the
  same identity for an invertible function on the generic fibre of an étale scheme over the
  target, read across a square of bases — on an integral scheme and on an arbitrary one.
* `Stacks.EtaleCohomology.weightedIntegerSkyscraperDirectImageMap_one`: with weight one the
  contribution of a point is the summand of the multiplicity-one map.
* `Stacks.EtaleCohomology.ι_ramifiedClosedPointDivisorDirectImageMap`: the weighted third
  component on the summand at a closed point of `Y`.

## References

* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1): the length identity for
  a flat local homomorphism that the order-of-vanishing identity rests on.
* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the divisor sequence
  whose third term the weighted map compares.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Order IsLocalRing AlgebraicGeometry
  AlgebraicGeometry.Scheme

universe u v

/-- Under a bijective ring homomorphism `φ : R → S`, the colength of an ideal `I` of `R` equals
the colength of `I.map φ`. -/
private theorem Module.length_quotient_eq_length_quotient_map {R S : Type*} [CommRing R]
    [CommRing S] (φ : R →+* S) (hφ : Function.Bijective φ) (I : Ideal R) :
    Module.length R (R ⧸ I) = Module.length S (S ⧸ I.map φ) := by
  let ψ : R →+* S ⧸ I.map φ := (Ideal.Quotient.mk (I.map φ)).comp φ
  have hψ : Function.Surjective ψ := Ideal.Quotient.mk_surjective.comp hφ.2
  have hker : RingHom.ker ψ = I := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective _ hφ.2,
      ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hφ.1, sup_bot_eq]
  let : Algebra R S := φ.toAlgebra
  let : Algebra R (S ⧸ I.map φ) := ψ.toAlgebra
  have : IsScalarTower R S (S ⧸ I.map φ) := IsScalarTower.of_algebraMap_eq' rfl
  have hone : Module.length R (R ⧸ RingHom.ker ψ) = Module.length R (S ⧸ I.map φ) :=
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Algebra.ofId R (S ⧸ I.map φ)) hψ).toLinearEquiv.length_eq
  rw [hker] at hone
  exact hone.trans (Module.length_eq_of_surjective (M := S ⧸ I.map φ) hφ.2)

namespace AlgebraicGeometry

/-- **The local multiplicity of a morphism of schemes at a point**: the length of
`𝒪_{X,x} / 𝔪_{Y,f(x)} 𝒪_{X,x}` as a module over `𝒪_{X,x}`. For an extension of discrete
valuation rings this is the exponent `e` in `𝔪_{Y,f(x)} 𝒪_{X,x} = 𝔪_{X,x}^e`. -/
def Scheme.Hom.ramificationLength {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : ℕ :=
  (Module.length (X.presheaf.stalk x)
    (X.presheaf.stalk x ⧸
      (maximalIdeal (Y.presheaf.stalk (f.base x))).map (f.stalkMap x).hom)).toNat

/-- The local multiplicity of `f` at `x` is the colength of the ideal of `𝒪_{X,x}` generated by
the image of `𝔪_{Y,f(x)}`, as a natural number. -/
theorem Scheme.Hom.ramificationLength_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    f.ramificationLength x =
      (Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸
          (maximalIdeal (Y.presheaf.stalk (f.base x))).map (f.stalkMap x).hom)).toNat :=
  rfl

/-- **The local multiplicity is one where the maximal ideal downstairs generates the maximal
ideal upstairs**: the quotient is then the residue field, a simple module. -/
theorem Scheme.Hom.ramificationLength_eq_one_of_map_maximalIdeal_eq {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X)
    (hmax : (maximalIdeal (Y.presheaf.stalk (f.base x))).map (f.stalkMap x).hom =
      maximalIdeal (X.presheaf.stalk x)) :
    f.ramificationLength x = 1 := by
  have hone : Module.length (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x)) = 1 :=
    Module.length_eq_one_iff.mpr (isSimpleModule_iff_quot_maximal.mpr
      ⟨maximalIdeal (X.presheaf.stalk x), maximalIdeal.isMaximal (X.presheaf.stalk x),
        ⟨LinearEquiv.refl _ _⟩⟩)
  rw [Scheme.Hom.ramificationLength_eq, hmax, hone]
  rfl

/-- **The local multiplicity is unchanged by restriction to opens**: if `f ≫ j = i ≫ f'` with `i`
and `j` open immersions, the local multiplicity of `f` at `z` is that of `f'` at `i z`. The two
extended maximal ideals correspond under the stalk isomorphism of `i`, and the colengths of
corresponding ideals under an isomorphism of local rings agree. -/
theorem Scheme.Hom.ramificationLength_of_comp_eq {A B C D : Scheme.{u}} {f : A ⟶ B} {f' : C ⟶ D}
    {i : A ⟶ C} {j : B ⟶ D} [IsOpenImmersion i] [IsOpenImmersion j] (hsq : f ≫ j = i ≫ f')
    (z : A) : f.ramificationLength z = f'.ramificationLength (i.base z) := by
  have e1 := Stacks.EtaleCohomology.map_maximalIdeal_stalkMap_congr hsq z
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at e1
  have e2 : (maximalIdeal (D.presheaf.stalk ((f ≫ j).base z))).map
      (j.stalkMap (f.base z) ≫ f.stalkMap z).hom =
      (maximalIdeal (B.presheaf.stalk (f.base z))).map (f.stalkMap z).hom := by
    rw [CommRingCat.hom_comp]
    exact (Ideal.map_map (j.stalkMap (f.base z)).hom (f.stalkMap z).hom).symm.trans
      (congrArg (Ideal.map (f.stalkMap z).hom)
        (Stacks.EtaleCohomology.map_maximalIdeal_of_isIso _))
  have e3 : (maximalIdeal (D.presheaf.stalk ((i ≫ f').base z))).map
      (f'.stalkMap (i.base z) ≫ i.stalkMap z).hom =
      ((maximalIdeal (D.presheaf.stalk (f'.base (i.base z)))).map
        (f'.stalkMap (i.base z)).hom).map (i.stalkMap z).hom := by
    rw [CommRingCat.hom_comp]
    exact (Ideal.map_map (f'.stalkMap (i.base z)).hom (i.stalkMap z).hom).symm
  rw [Scheme.Hom.ramificationLength_eq, Scheme.Hom.ramificationLength_eq,
    e2.symm.trans (e1.trans e3),
    ← Module.length_quotient_eq_length_quotient_map (i.stalkMap z).hom
      (ConcreteCategory.bijective_of_isIso (i.stalkMap z))
      ((maximalIdeal (D.presheaf.stalk (f'.base (i.base z)))).map (f'.stalkMap (i.base z)).hom)]

end AlgebraicGeometry

namespace Stacks.Chow

/-- **The order of vanishing of a pulled back rational function is the local multiplicity times
the order of vanishing**, at a point `z` of a flat dominant morphism whose codimension equals
that of its image: `ord_z(f^# g) = e_z · ord_{f z}(g)`.

The colength of a principal ideal generated by an element coming from downstairs multiplies, under
a flat local stalk map, by the colength of the extended maximal ideal (Stacks 02M1), which is the
local multiplicity; writing `g` as a quotient of two elements of the local ring at `f z` turns
that into the identity of orders. Away from codimension one both sides vanish. -/
theorem ord_dominantFunctionFieldMap_eq_ramificationLength_mul {U V : Scheme.{u}} (f : U ⟶ V)
    [Flat f] [IsIntegral U] [IsIntegral V] [IsLocallyNoetherian U] [IsLocallyNoetherian V]
    [IsDominant f] (z : U) (hcoh : coheight (f.base z) = coheight z) (g : V.functionField) :
    U.ord (dominantFunctionFieldMap f g) z =
      (f.ramificationLength z : ℤ) * V.ord g (f.base z) := by
  have hlen : ∀ a : V.presheaf.stalk (f.base z),
      ((Module.length (U.presheaf.stalk z)
          (U.presheaf.stalk z ⧸ Ideal.span {(f.stalkMap z).hom a})).toNat : ℤ) =
        (f.ramificationLength z : ℤ) *
          ((Module.length (V.presheaf.stalk (f.base z))
            (V.presheaf.stalk (f.base z) ⧸ Ideal.span {a})).toNat : ℤ) := by
    intro a
    algebraize [(f.stalkMap z).hom]
    have hloc : IsLocalHom (algebraMap (V.presheaf.stalk (f.base z)) (U.presheaf.stalk z)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap z).hom)
    have hflat : Module.Flat (V.presheaf.stalk (f.base z)) (U.presheaf.stalk z) :=
      RingHom.flat_algebraMap_iff.mp (Flat.stalkMap f z)
    have halg : algebraMap (V.presheaf.stalk (f.base z)) (U.presheaf.stalk z) =
        (f.stalkMap z).hom := RingHom.algebraMap_toAlgebra _
    have hram : extendedMaximalIdeal (V.presheaf.stalk (f.base z)) (U.presheaf.stalk z) =
        (maximalIdeal (V.presheaf.stalk (f.base z))).map (f.stalkMap z).hom :=
      congrArg (fun φ => Ideal.map φ (maximalIdeal (V.presheaf.stalk (f.base z)))) halg
    have hcoe : (f.stalkMap z).hom a =
        algebraMap (V.presheaf.stalk (f.base z)) (U.presheaf.stalk z) a := rfl
    rw [hcoe, AlgebraicGeometry.length_quotient_span_algebraMap a, hram, ENat.toNat_mul,
      Nat.cast_mul, ← f.ramificationLength_eq z]
    exact mul_comm _ _
  by_cases hz : coheight z = 1
  · by_cases hg : g = 0
    · simp [hg]
    have hzV : coheight (f.base z) = 1 := hcoh.trans hz
    obtain ⟨a, b, ha, hb, hrep⟩ := exists_div_algebraMap_stalk_eq (f.base z) hg
    rw [← hrep, ord_dominantFunctionFieldMap_eq_length_sub f hz ha hb,
      ord_div_algebraMap_eq_length_sub hzV ha hb, hlen a, hlen b, mul_sub]
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hz,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h ↦ hz (hcoh.symm.trans h)), mul_zero]

end Stacks.Chow

namespace Stacks.EtaleCohomology

section Integral

variable {X X' U V : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace X'] [IsIntegral U]
  [IsIntegral V] [IsLocallyNoetherian U] [IsLocallyNoetherian V] (gU : U ⟶ X') (gV : V ⟶ X)
  [Flat gU] [Flat gV] (h : U ⟶ V) [Flat h]
  (m : pullback gU (genericPointInclusion X') ⟶ pullback gV (genericPointInclusion X))
  (hm : m ≫ pullback.fst gV (genericPointInclusion X) =
    pullback.fst gU (genericPointInclusion X') ≫ h)

include hm in
/-- **The order of vanishing across a square of bases is the local multiplicity times the order
of vanishing downstairs**, at a point `y` where the codimension is preserved. This is the
pointwise content of the third square of a morphism of divisor sequences along a ramified
cover. -/
theorem genericFibreOrd_appTop_eq_ramificationLength_mul_of_square (y : U)
    (hcoh : coheight (h.base y) = coheight y)
    (a : (Γ(pullback gV (genericPointInclusion X), ⊤))ˣ) :
    genericFibreOrd gU y (Additive.ofMul (Units.map m.appTop.hom.toMonoidHom a)) =
      (h.ramificationLength y : ℤ) * genericFibreOrd gV (h.base y) (Additive.ofMul a) := by
  have : IsDominant h := ((tfae_isDominant_of_isIntegral h).out 1 2).mpr
    (base_genericPoint_eq_genericPoint_of_flat h)
  rw [genericFibreOrd_apply, genericFibreOrd_apply]
  change Scheme.ord (genericFibreToFunctionField gU
    (m.appTop (a : Γ(pullback gV (genericPointInclusion X), ⊤)))) y = _
  rw [genericFibreToFunctionField_appTop_of_square gU gV h m hm,
    Stacks.Chow.ord_dominantFunctionFieldMap_eq_ramificationLength_mul h y hcoh]
  rfl

end Integral

section Point

variable {X X' Y Z : Scheme.{u}} [IsIntegral X] [IsNormal X] [IsIntegral X'] [IsNormal X']
  (gY : Y ⟶ X') (gZ : Z ⟶ X) [Etale gY] [Etale gZ] [IsLocallyNoetherian Y]
  [IsLocallyNoetherian Z] (h : Y ⟶ Z) [Flat h]
  (m : pullback gY (genericPointInclusion X') ⟶ pullback gZ (genericPointInclusion X))
  (hm : m ≫ pullback.fst gZ (genericPointInclusion X) =
    pullback.fst gY (genericPointInclusion X') ≫ h)

include hm in
/-- **The order of vanishing across a square of étale schemes over two bases is the local
multiplicity times the order of vanishing downstairs**, at a point `y` where the codimension is
preserved. Integral opens `W_Y ≤ h⁻¹ W_Z` around `y` and its image reduce this to
`Stacks.EtaleCohomology.genericFibreOrd_appTop_eq_ramificationLength_mul_of_square`, the local
multiplicity being unchanged by the restriction
(`AlgebraicGeometry.Scheme.Hom.ramificationLength_of_comp_eq`). -/
theorem genericFibreOrdOfPoint_appTop_eq_ramificationLength_mul_of_square (y : Y)
    (hcoh : coheight (h.base y) = coheight y)
    (a : (Γ(pullback gZ (genericPointInclusion X), ⊤))ˣ) :
    genericFibreOrdOfPoint gY y (Additive.ofMul (Units.map m.appTop.hom.toMonoidHom a)) =
      (h.ramificationLength y : ℤ) *
        genericFibreOrdOfPoint gZ (h.base y) (Additive.ofMul a) := by
  obtain ⟨WY, WZ, hyWY, hWZ, hle, hWY, hWZi⟩ := exists_isIntegral_opens_square gY gZ h y
  have h1 := opensRestrict_ι h hle
  have hbase' : WZ.ι.base ((opensRestrict h hle).base ⟨y, hyWY⟩) = h.base (WY.ι.base ⟨y, hyWY⟩) :=
    congrArg (fun φ : WY.toScheme ⟶ Z => φ.base ⟨y, hyWY⟩) h1
  have hbase : (opensRestrict h hle).base ⟨y, hyWY⟩ = ⟨h.base y, hWZ⟩ := Subtype.ext hbase'
  have hram : (opensRestrict h hle).ramificationLength ⟨y, hyWY⟩ = h.ramificationLength y :=
    Scheme.Hom.ramificationLength_of_comp_eq h1 ⟨y, hyWY⟩
  rw [genericFibreOrdOfPoint_square_eq gY gZ h m hm y hyWY hle a,
    genericFibreOrdOfPoint_eq_genericFibreOrdOfOpen gZ (W := WZ) ⟨h.base y, hWZ⟩,
    genericFibreOrdOfOpen_apply_ofMul, ← hbase, ← hram]
  have hcoh' := (coheight_eq_of_etale WZ.ι ((opensRestrict h hle).base ⟨y, hyWY⟩)).symm.trans
    ((congrArg coheight hbase').trans (hcoh.trans (coheight_eq_of_etale WY.ι ⟨y, hyWY⟩)))
  exact genericFibreOrd_appTop_eq_ramificationLength_mul_of_square (WY.ι ≫ gY) (WZ.ι ≫ gZ)
    (opensRestrict h hle) _ (genericFibreSquareOpensMap_fst gY gZ h m hm hle) ⟨y, hyWY⟩ hcoh' _

end Point

section Weighted

variable {X Y : Scheme.{u}} (π : X ⟶ Y)

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

/-- **The contribution of a single closed point `x` of `X` above `y`, with a weight `e`**, to a
morphism `⨁_y i_{y,*} 𝐙 ⟶ π_* (⨁_x i_{x,*} 𝐙)`: `e` times
`Stacks.EtaleCohomology.integerSkyscraperDirectImageMap` at `x`, followed by the inclusion of the
summand at `x`. -/
def weightedIntegerSkyscraperDirectImageMap (x : closedPoints X) (y : closedPoints Y)
    (hxy : π.base x.1 = y.1) (e : ℤ) :
    closedPointSkyscraper.{u, v} Y y ⟶
      (etaleAbelianDirectImage.{u, v} π).obj (closedPointDivisorSheaf.{u, v} X) :=
  e • (eqToHom (by rw [closedPointSkyscraper, hxy]) ≫
    integerSkyscraperDirectImageMap.{u, v} π x.1 ≫
      (etaleAbelianDirectImage.{u, v} π).map (closedPointDivisorSheaf.ι.{u, v} X x))

/-- **With weight one the contribution of a closed point is the summand at that point of the
multiplicity-one map** `Stacks.EtaleCohomology.closedPointDivisorDirectImageMap`, which takes a
choice of one closed point above each closed point of `Y`. -/
theorem weightedIntegerSkyscraperDirectImageMap_one (σ : closedPoints Y → closedPoints X)
    (hσ : ∀ y, π.base (σ y).1 = y.1) (y : closedPoints Y) :
    weightedIntegerSkyscraperDirectImageMap.{u, v} π (σ y) y (hσ y) 1 =
      closedPointDivisorSheaf.ι.{u, v} Y y ≫
        closedPointDivisorDirectImageMap.{u, v} π σ hσ := by
  rw [ι_closedPointDivisorDirectImageMap]
  exact one_smul ℤ _

/-- **The ramification-weighted third component of a morphism of divisor sequences**,
`⨁_{y ∈ Y_0} i_{y,*} 𝐙 ⟶ π_* (⨁_{x ∈ X_0} i_{x,*} 𝐙)`: the summand at a closed point `y` is sent
to the sum over the closed points `x` in the finite family `F y` above `y` of
`Scheme.Hom.ramificationLength` at `x` times the skyscraper direct image map at `x`. -/
def ramifiedClosedPointDivisorDirectImageMap (F : closedPoints Y → Finset (closedPoints X))
    (hF : ∀ (y : closedPoints Y) (x : closedPoints X), x ∈ F y → π.base x.1 = y.1) :
    closedPointDivisorSheaf.{u, v} Y ⟶
      (etaleAbelianDirectImage.{u, v} π).obj (closedPointDivisorSheaf.{u, v} X) :=
  Sigma.desc fun y => ∑ x ∈ (F y).attach,
    weightedIntegerSkyscraperDirectImageMap.{u, v} π x.1 y (hF y x.1 x.2)
      (π.ramificationLength x.1.1)

/-- **The weighted third component on the summand at a closed point of `Y`.** -/
theorem ι_ramifiedClosedPointDivisorDirectImageMap
    (F : closedPoints Y → Finset (closedPoints X))
    (hF : ∀ (y : closedPoints Y) (x : closedPoints X), x ∈ F y → π.base x.1 = y.1)
    (y : closedPoints Y) :
    closedPointDivisorSheaf.ι.{u, v} Y y ≫
        ramifiedClosedPointDivisorDirectImageMap.{u, v} π F hF =
      ∑ x ∈ (F y).attach,
        weightedIntegerSkyscraperDirectImageMap.{u, v} π x.1 y (hF y x.1 x.2)
          (π.ramificationLength x.1.1) :=
  Sigma.ι_comp_desc _ y

end Weighted

end Stacks.EtaleCohomology

end
