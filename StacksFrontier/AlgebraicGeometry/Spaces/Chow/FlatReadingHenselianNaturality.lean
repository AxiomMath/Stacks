module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentFlatRationalFunctionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties

/-!
# The reading of a rational function along a flat morphism, at the henselian local ring

Let `f : X ⟶ Y` be a flat morphism of decent, locally Noetherian algebraic spaces over `S`, with
`Y` integral, and let `Z ⊆ X` be a prime divisor with generic point `ξ`. A rational function `g`
of `Y` has a reading `ĝ` in the total ring of fractions `Q(𝒪^h_{X, ξ})` of the henselian local
ring of Stacks 0ENK, obtained by reading `g` on the generic chart of `Z`, which is flat over `Y`
(`AlgebraicGeometry.Space.PrimeDivisor.rationalFunctionsToGenericTotalFractionRingOfFlat`). `X`
is **not** assumed integral, so this reading replaces the embedding of Stacks 0ENK of the
pullback `g ∘ f`, which is not defined.

This file proves two facts about `ĝ`:

* the reading may be computed on **any** affine elementary étale neighbourhood of `ξ`, not only
  on the generic chart
  (`PrimeDivisor.rationalFunctionsToGenericTotalFractionRingOfFlat_eq_neighborhood`);
* when `ξ` lies over the generic point `ξ'` of a prime divisor `Z'` of `Y`, the reading is the
  image of the embedding of Stacks 0ENK of `g` under the map of total rings of fractions induced
  by a flat local homomorphism `φ : 𝒪^h_{Y, ξ'} ⟶ 𝒪^h_{X, ξ}` induced by `f`, and the colength
  of `𝔪_{Y, ξ'} 𝒪^h_{X, ξ}` is the colength of the extended maximal ideal on a square of étale
  charts over `f`
  (`PrimeDivisor.exists_henselianLocalRingHom_rationalFunctionsToGenericTotalFractionRingOfFlat`).

## Main results

* `AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRingOfFlat_comp`: the reading on a
  flat chart restricts along a morphism of flat charts.
* `PrimeDivisor.rationalFunctionsToGenericTotalFractionRingOfFlat_eq_neighborhood`:
  the reading at `ξ` computed on an arbitrary affine elementary étale neighbourhood.
* `PrimeDivisor.exists_henselianLocalRingHom_rationalFunctionsToGenericTotalFractionRingOfFlat`:
  the naturality square of the reading along `f`, together with the colength of `φ` read on a
  square of étale charts.

## References

* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 0BGV](https://stacks.math.columbia.edu/tag/0BGV)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Restriction of the reading on a flat chart -/

section Restriction

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hintY : IsIntegralSpace B S hS Y)
    {U V : BigFppfOver B S hS} [IsAffine U.left.1] [IsLocallyNoetherian U.left.1]
    [IsAffine V.left.1] [IsLocallyNoetherian V.left.1]

/-- **The reading of a rational function on a flat chart restricts along a morphism of flat
charts.** If `cU : U → Y` and `cV : V → Y` are flat affine locally Noetherian charts of an
integral algebraic space and `j : U → V` is a morphism of the site with `j ≫ cV = cU`, along
which restriction of global sections carries nonzerodivisors to nonzerodivisors, then the
reading of `g` in `Q(Γ(U, 𝒪_U))` is the restriction along `j` of its reading in
`Q(Γ(V, 𝒪_V))`. -/
theorem rationalFunctionsToTotalFractionRingOfFlat_comp
    (cU : yoneda.obj U ⟶ Y) (hcU : IsFlat B S hS cU)
    (cV : yoneda.obj V ⟶ Y) (hcV : IsFlat B S hS cV) (j : U ⟶ V)
    (hsq : yoneda.map j ≫ cV = cU)
    (hj : (Γ(V.left.1, ⊤))⁰ ≤ ((Γ(U.left.1, ⊤))⁰).comap (chartGlobalSectionsRestrict B S hS j))
    (g : rationalFunctions B S hS hY) :
    rationalFunctionsToTotalFractionRingOfFlat B S hS hY hintY U cU hcU g =
      chartFractionMap B S hS j hj
        (rationalFunctionsToTotalFractionRingOfFlat B S hS hY hintY V cV hcV g) := by
  have hmU := factorsThroughDenseOpens_totalFractionObject_of_isFlat B S hS hY hintY U cU hcU
  have hmV := factorsThroughDenseOpens_totalFractionObject_of_isFlat B S hS hY hintY V cV hcV
  have hmV' := hmV.comp B S hS hY (totalFractionObjectMapOfHom B S hS j hj)
  have hmor : yoneda.map (totalFractionObjectMapOfHom B S hS j hj) ≫
        (yoneda.map (totalFractionObjectMap B S hS V) ≫ cV) =
      yoneda.map (totalFractionObjectMap B S hS U) ≫ cU := by
    rw [← Category.assoc, ← Functor.map_comp, totalFractionObjectMapOfHom_comp B S hS j hj,
      Functor.map_comp, Category.assoc, hsq]
  rw [rationalFunctionsToTotalFractionRingOfFlat_eq_ΓSpecIso B S hS hY hintY U cU hcU hmU,
    rationalFunctionsToTotalFractionRingOfFlat_eq_ΓSpecIso B S hS hY hintY V cV hcV hmV,
    ← evalSiteRingHom_congr_mor B S hS hY hmor hmV' hmU g,
    evalSiteRingHom_naturality B S hS hY (totalFractionObjectMapOfHom B S hS j hj) hmV hmV' g]
  exact Scheme.ΓSpecIso_hom_appTop_ofHom_apply (chartFractionMap B S hS j hj) _

end Restriction

/-! ### The reading at the generic point of a prime divisor, on any affine neighbourhood -/

section Neighborhood

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun W : Scheme.{u} => IsLocallyNoetherian W))
    (Z : PrimeDivisor B S hS X)

/-- An elementary étale neighbourhood is an étale chart, in the form in which the flatness of a
morphism of algebraic spaces is tested. -/
theorem ElementaryEtaleNeighborhood.presheaf_etale_toSpace {x : points B S hS X}
    (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf U.toSpace := by
  simpa using U.etale_toSpace U.scheme (𝟙 _) (presheaf_etale_id B S hS U.scheme)

/-- A morphism of elementary étale neighbourhoods is a flat morphism of schemes: it is a
morphism of étale charts over the identity of `X`, which is flat. -/
theorem ElementaryEtaleNeighborhood.flat_hom {x : points B S hS X}
    {T U : ElementaryEtaleNeighborhood B S hS X hX x} (c : T ⟶ U) :
    AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map c.hom) :=
  isFlat_id B S hS hX T.scheme U.scheme T.toSpace U.toSpace c.hom
    (ElementaryEtaleNeighborhood.presheaf_etale_toSpace B S hS hX T)
    (ElementaryEtaleNeighborhood.presheaf_etale_toSpace B S hS hX U)
    (by rw [c.over, Category.comp_id])

/-- Restriction of global sections along a morphism of affine elementary étale neighbourhoods
carries nonzerodivisors to nonzerodivisors, the morphism being flat. -/
theorem ElementaryEtaleNeighborhood.nonZeroDivisors_le_comap_hom {x : points B S hS X}
    {T U : ElementaryEtaleNeighborhood B S hS X hX x} [IsAffine T.scheme.left.1]
    [IsAffine U.scheme.left.1] (c : T ⟶ U) :
    (Γ(U.scheme.left.1, ⊤))⁰ ≤ ((Γ(T.scheme.left.1, ⊤))⁰).comap
      (chartGlobalSectionsRestrict B S hS c.hom) := by
  have : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map c.hom) :=
    ElementaryEtaleNeighborhood.flat_hom B S hS hX c
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T.scheme) := ‹IsAffine T.scheme.left.1›
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.scheme) := ‹IsAffine U.scheme.left.1›
  exact fun _ hc => Ring.map_mem_nonZeroDivisors_of_flatHom
    (Scheme.Hom.flat_appTop ((BigFppfOver.toScheme B S hS).map c.hom)) hc

/-- The map of total rings of fractions of Stacks 0EMY composed with restriction along a morphism
of affine elementary étale neighbourhoods `c : T ⟶ U` of the generic point of a prime divisor is
the map for `U`: on global sections this is the naturality of Stacks 0EMY in the
neighbourhood. -/
theorem PrimeDivisor.neighborhoodTotalFractionRingToGeneric_comp_chartFractionMap
    [IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    {T U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X)}
    [IsAffine T.scheme.left.1] [IsAffine U.scheme.left.1] (c : T ⟶ U)
    (hCof : IsCofiltered (ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X)))
    (y : FractionRing Γ(U.scheme.left.1, ⊤)) :
    Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec T hCof
        (chartFractionMap B S hS c.hom
          (ElementaryEtaleNeighborhood.nonZeroDivisors_le_comap_hom B S hS hX c) y) =
      Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec U hCof y := by
  have h : (Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec T hCof).comp
        (chartFractionMap B S hS c.hom
          (ElementaryEtaleNeighborhood.nonZeroDivisors_le_comap_hom B S hS hX c)) =
      Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec U hCof := by
    refine IsLocalization.ringHom_ext (Γ(U.scheme.left.1, ⊤))⁰ (RingHom.ext fun a => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, chartFractionMap_algebraMap,
      PrimeDivisor.neighborhoodTotalFractionRingToGeneric,
      PrimeDivisor.neighborhoodTotalFractionRingToGeneric, IsLocalization.map_eq,
      IsLocalization.map_eq]
    exact congrArg _ (Z.neighborhoodSectionsToGenericHenselianLocalRing_naturality B S hS hX hdec
      c a)
  exact RingHom.congr_fun h y

section Reading

variable {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)
    (hintT : IsIntegralSpace B S hS T) (f : X ⟶ T) (hf : IsFlat B S hS f)

/-- The reading of a rational function of `T` on an elementary étale neighbourhood `U` of a
point of `X`, the chart `U → X → T` being flat. -/
abbrev neighborhoodFlatReading {x : points B S hS X}
    (U : ElementaryEtaleNeighborhood B S hS X hX x) [IsAffine U.scheme.left.1]
    [IsLocallyNoetherian U.scheme.left.1] :
    rationalFunctions B S hS hT →+* FractionRing Γ(U.scheme.left.1, ⊤) :=
  rationalFunctionsToTotalFractionRingOfFlat B S hS hT hintT U.scheme (U.toSpace ≫ f)
    (isFlat_comp B S hS (isAlgebraicSpace_yoneda B S hS U.scheme) hX hT U.toSpace f
      (isFlat_of_isEtale B S hS U.etale_toSpace) hf)

/-- The reading of a rational function of `T` at the generic point of a prime divisor of `X`,
pushed into `Q(𝒪^h_{X, ξ})`, is unchanged by refining an affine neighbourhood. -/
theorem PrimeDivisor.neighborhoodTotalFractionRingToGeneric_neighborhoodFlatReading_comp
    [IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    {V U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X)}
    [IsAffine V.scheme.left.1] [IsLocallyNoetherian V.scheme.left.1]
    [IsAffine U.scheme.left.1] [IsLocallyNoetherian U.scheme.left.1] (c : V ⟶ U)
    (hCof : IsCofiltered (ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X)))
    (g : rationalFunctions B S hS hT) :
    Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec V hCof
        (neighborhoodFlatReading B S hS hX hT hintT f hf V g) =
      Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec U hCof
        (neighborhoodFlatReading B S hS hX hT hintT f hf U g) := by
  rw [neighborhoodFlatReading, neighborhoodFlatReading,
    rationalFunctionsToTotalFractionRingOfFlat_comp B S hS hT hintT (V.toSpace ≫ f) _
      (U.toSpace ≫ f) _ c.hom (by rw [← Category.assoc, c.over])
      (ElementaryEtaleNeighborhood.nonZeroDivisors_le_comap_hom B S hS hX c) g]
  exact Z.neighborhoodTotalFractionRingToGeneric_comp_chartFractionMap B S hS hX hdec c hCof _

/-- **The reading at the generic point of a prime divisor, on any affine neighbourhood.** The
reading `AlgebraicGeometry.Space.PrimeDivisor.rationalFunctionsToGenericTotalFractionRingOfFlat`
of a rational function of `T` at the generic point `ξ` of a prime divisor of `X`, defined on the
generic chart, is computed on any affine elementary étale neighbourhood of `ξ`: two such are
refined by a common affine one (Stacks 0BGV), and refining does not change the value. -/
theorem PrimeDivisor.rationalFunctionsToGenericTotalFractionRingOfFlat_eq_neighborhood
    (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))
    [IsAffine U.scheme.left.1] (g : rationalFunctions B S hS hT) :
    letI := Z.isLocallyNoetherian_chart B S hS hX hN U
    letI : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
      henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    Z.rationalFunctionsToGenericTotalFractionRingOfFlat B S hS hX hdec hN hT hintT f hf g =
      Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec U
        (ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS X hX
          (Z.genericPoint B S hS X) ⟨Z.genericChart B S hS hX hdec⟩)
        (neighborhoodFlatReading B S hS hX hT hintT f hf U g) := by
  let := Z.isLocallyNoetherian_chart B S hS hX hN U
  let : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  let := Z.isLocallyNoetherian_genericChart B S hS hX hdec hN
  obtain ⟨W, a, b, hW⟩ := ElementaryEtaleNeighborhood.exists_affine_cone_objs B S hS X hX
    (Z.genericPoint B S hS X) U (Z.genericChart B S hS hX hdec)
  let := hW
  let := Z.isLocallyNoetherian_chart B S hS hX hN W
  have hgen : Z.rationalFunctionsToGenericTotalFractionRingOfFlat B S hS hX hdec hN hT hintT f
      hf g = Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec
        (Z.genericChart B S hS hX hdec)
        (ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS X hX
          (Z.genericPoint B S hS X) ⟨Z.genericChart B S hS hX hdec⟩)
        (neighborhoodFlatReading B S hS hX hT hintT f hf (Z.genericChart B S hS hX hdec) g) :=
    rfl
  rw [hgen, ← Z.neighborhoodTotalFractionRingToGeneric_neighborhoodFlatReading_comp B S hS hX
      hdec hT hintT f hf b,
    Z.neighborhoodTotalFractionRingToGeneric_neighborhoodFlatReading_comp B S hS hX hdec hT
      hintT f hf a]

end Reading

/-! ### The naturality square along a flat morphism, with its colength -/

section Square

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hdecY : IsDecentSpace B S hS Y) (hintY : IsIntegralSpace B S hS Y)
    (hNY : HasEtaleLocalProperty B S hS Y (fun W : Scheme.{u} => IsLocallyNoetherian W))
    (W : PrimeDivisor B S hS Y) (f : X ⟶ Y) (hf : IsFlat B S hS f)

/-- The image of the maximal ideal under an isomorphism of local rings is the maximal ideal. -/
private theorem map_maximalIdeal_of_iso {R R' : CommRingCat.{u}} [IsLocalRing R]
    [IsLocalRing R'] (e : R ≅ R') :
    Ideal.map e.hom.hom (maximalIdeal R) = maximalIdeal R' :=
  IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e.commRingCatIsoToRingEquiv
    (p := maximalIdeal R))

/-- Restriction of global sections along a composite of a refinement and a square over a flat
morphism carries nonzerodivisors to nonzerodivisors. -/
private theorem nonZeroDivisors_le_comap_of_isFlat_square (hf : IsFlat B S hS f)
    {x : points B S hS X} {y : points B S hS Y} (U : ElementaryEtaleNeighborhood B S hS X hX x)
    (V : ElementaryEtaleNeighborhood B S hS Y hY y) [IsAffine U.scheme.left.1]
    [IsAffine V.scheme.left.1] (j : U.scheme ⟶ V.scheme)
    (hsq : yoneda.map j ≫ V.toSpace = U.toSpace ≫ f) :
    (Γ(V.scheme.left.1, ⊤))⁰ ≤ ((Γ(U.scheme.left.1, ⊤))⁰).comap
      (chartGlobalSectionsRestrict B S hS j) := by
  have : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map j) :=
    hf U.scheme V.scheme U.toSpace V.toSpace j
      (ElementaryEtaleNeighborhood.presheaf_etale_toSpace B S hS hX U)
      (ElementaryEtaleNeighborhood.presheaf_etale_toSpace B S hS hY V) hsq
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.scheme) := ‹IsAffine U.scheme.left.1›
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.scheme) := ‹IsAffine V.scheme.left.1›
  exact fun _ hc => Ring.map_mem_nonZeroDivisors_of_flatHom
    (Scheme.Hom.flat_appTop ((BigFppfOver.toScheme B S hS).map j)) hc

/-- A compatible local homomorphism of henselian local rings is compatible with the maps from the
global sections of a square of neighbourhoods, the neighbourhood of the source being refined. -/
private theorem map_stalkToHenselianLocalRing_germ_eq_neighborhoodSections
    {y : points B S hS Y} (hdecY : IsDecentSpace B S hS Y)
    {V : ElementaryEtaleNeighborhood B S hS Y hY y}
    {U₀ U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X)}
    (j₀ : U₀.scheme ⟶ V.scheme) (hj₀ : j₀.left.1 U₀.point = V.point) (r : U ⟶ U₀)
    (φ : (henselianLocalRing B S hS Y hY y hdecY : Type (u + 1)) →+*
      (henselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec : Type (u + 1)))
    (hcompat₀ : ∀ a, φ (stalkToHenselianLocalRing B S hS Y hY y hdecY V a) =
      stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U₀
        (((V.scheme.left.1.presheaf.stalkCongr (.of_eq hj₀.symm)).hom ≫
          j₀.left.1.stalkMap U₀.point).hom a))
    (a : Γ(V.scheme.left.1, ⊤)) :
    φ (stalkToHenselianLocalRing B S hS Y hY y hdecY V
        (V.scheme.left.1.presheaf.germ ⊤ V.point trivial a)) =
      Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U
        (chartGlobalSectionsRestrict B S hS (r.hom ≫ j₀) a) := by
  have h1 := hcompat₀ (V.scheme.left.1.presheaf.germ ⊤ V.point trivial a)
  rw [germ_top_stalkCongr_stalkMap j₀.left.1 hj₀ a] at h1
  have h2 := Z.neighborhoodSectionsToGenericHenselianLocalRing_naturality B S hS hX hdec r
    (j₀.left.1.appTop a)
  rw [show chartGlobalSectionsRestrict B S hS (r.hom ≫ j₀) a =
      r.hom.left.1.appTop (j₀.left.1.appTop a) by
    rw [chartGlobalSectionsRestrict, Functor.map_comp, Scheme.Hom.comp_appTop]; rfl, h2]
  exact h1

include hintY in
/-- **The reading of a rational function along a flat morphism, at the henselian local ring,
is natural.** Let `f : X ⟶ Y` be a flat morphism of decent, locally Noetherian algebraic spaces
over `S` with `Y` integral, let `Z ⊆ X` and `W ⊆ Y` be prime divisors and suppose the generic
point `ξ` of `Z` lies over the generic point `η` of `W`. There is a flat local homomorphism
`φ : 𝒪^h_{Y, η} ⟶ 𝒪^h_{X, ξ}` such that

* for every rational function `g` of `Y`, the reading of `g` at `ξ` is the image under `Q(φ)`
  of the embedding of Stacks 0ENK of `g` at `η`; and
* there is a square of elementary étale neighbourhoods `j : U → V` over `f`, of `ξ` and of `η`,
  on which the colength of `𝔪_{Y, η} 𝒪^h_{X, ξ}` is the colength of `𝔪_{V, v} 𝒪_{U, u}`. -/
theorem PrimeDivisor.exists_henselianLocalRingHom_rationalFunctionsToGenericTotalFractionRingOfFlat
    (hZ : pointsMap B S hS X f (Z.genericPoint B S hS X) = W.genericPoint B S hS Y) :
    letI := henselianLocalRing_isLocalRing B S hS Y hY (W.genericPoint B S hS Y) hdecY
    ∃ (φ : ↥(W.genericHenselianLocalRing B S hS hY hdecY) →+*
        ↥(Z.genericHenselianLocalRing B S hS hX hdec)) (_ : IsLocalHom φ) (hφ : φ.Flat),
      (∀ g : rationalFunctions B S hS hY,
        Z.rationalFunctionsToGenericTotalFractionRingOfFlat B S hS hX hdec hN hY hintY f hf g =
          IsLocalization.map (T := (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰)
            (Z.genericTotalFractionRing B S hS hX hdec) φ
            (fun _ hc => Ring.map_mem_nonZeroDivisors_of_flatHom hφ hc)
            (W.rationalFunctionsToGenericTotalFractionRing B S hS hY hdecY hintY hNY g)) ∧
      ∃ (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))
        (V : ElementaryEtaleNeighborhood B S hS Y hY (W.genericPoint B S hS Y))
        (j : U.scheme ⟶ V.scheme),
        yoneda.map j ≫ V.toSpace = U.toSpace ≫ f ∧
        primeDivisorFlatMultiplicity B S hS hX hdec Z hY hdecY W φ =
          Module.length (U.scheme.left.1.presheaf.stalk U.point)
            (U.scheme.left.1.presheaf.stalk U.point ⧸
              Ideal.map (j.left.1.stalkMap U.point).hom
                (maximalIdeal (V.scheme.left.1.presheaf.stalk (j.left.1 U.point)))) := by
  let := henselianLocalRing_isLocalRing B S hS Y hY (W.genericPoint B S hS Y) hdecY
  let : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  have key := exists_henselianLocalRingHom_affineChartSquare B S hS hX hdec hY hdecY f
    (Z.genericPoint B S hS X)
  rw [hZ] at key
  obtain ⟨V, U₀, j₀, hj₀, φ, hsq₀, hVaff, hφloc, hcompat₀, hφflat⟩ := key
  refine ⟨φ, hφloc, hφflat hf, ?_, U₀, V, j₀, hsq₀, ?_⟩
  · obtain ⟨U, r, hUaff⟩ := ElementaryEtaleNeighborhood.exists_affine_refinement B S hS X hX
      (Z.genericPoint B S hS X) U₀
    have : IsAffine V.scheme.left.1 := hVaff
    have : IsAffine U.scheme.left.1 := hUaff
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.scheme) := hUaff
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.scheme) := hVaff
    have := Z.isLocallyNoetherian_chart B S hS hX hN U
    have := W.isReduced_chart B S hS hY hintY V
    have := W.isLocallyNoetherian_chart B S hS hY hNY V
    have hsq : yoneda.map (r.hom ≫ j₀) ≫ V.toSpace = U.toSpace ≫ f := by
      rw [Functor.map_comp, Category.assoc, hsq₀, ← Category.assoc, r.over]
    have hj := nonZeroDivisors_le_comap_of_isFlat_square B S hS hX hY f hf U V (r.hom ≫ j₀) hsq
    have hcompat : ∀ a : Γ(V.scheme.left.1, ⊤),
        φ (W.neighborhoodSectionsToGenericHenselianLocalRing B S hS hY hdecY V a) =
          Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U
            (chartGlobalSectionsRestrict B S hS (r.hom ≫ j₀) a) :=
      map_stalkToHenselianLocalRing_germ_eq_neighborhoodSections B S hS hX hdec Z hY _ j₀ hj₀ r φ
        hcompat₀
    have hCofX := ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS X hX
      (Z.genericPoint B S hS X) ⟨Z.genericChart B S hS hX hdec⟩
    have hCofY := ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS Y hY
      (W.genericPoint B S hS Y) ⟨V⟩
    intro g
    rw [Z.rationalFunctionsToGenericTotalFractionRingOfFlat_eq_neighborhood B S hS hX hdec hN
        hY hintY f hf U g, neighborhoodFlatReading,
      rationalFunctionsToTotalFractionRingOfFlat_comp B S hS hY hintY (U.toSpace ≫ f) _
        V.toSpace (isFlat_of_isEtale B S hS V.etale_toSpace) (r.hom ≫ j₀) hsq hj g,
      ← W.neighborhoodTotalFractionRingToGeneric_pullback_eq B S hS hY hdecY hintY hNY V hCofY]
    exact neighborhoodTotalFractionRingToGeneric_chartFractionMap B S hS hX hY hdec hdecY Z W U
      V hCofX hCofY (r.hom ≫ j₀) hj φ _ hcompat _
  · let := stalkAlgebra B S hS X hX (Z.genericPoint B S hS X) hdec U₀
    have : IsLocalRing.IsHenselization (U₀.scheme.left.1.presheaf.stalk U₀.point)
        (ResidueField (U₀.scheme.left.1.presheaf.stalk U₀.point))
        ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
      henselianLocalRing_isHenselization B S hS X hX (Z.genericPoint B S hS X) hdec U₀
    have : Module.Flat (U₀.scheme.left.1.presheaf.stalk U₀.point)
        ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
      IsLocalRing.IsHenselization.flat
        (L := ResidueField (U₀.scheme.left.1.presheaf.stalk U₀.point))
    have : IsLocalHom (algebraMap (U₀.scheme.left.1.presheaf.stalk U₀.point)
        ↥(Z.genericHenselianLocalRing B S hS hX hdec)) :=
      isLocalHom_stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U₀
    have hmaxU := map_maximalIdeal_stalkToHenselianLocalRing B S hS X hX
      (Z.genericPoint B S hS X) hdec U₀
    have hmaxV := map_maximalIdeal_stalkToHenselianLocalRing B S hS Y hY
      (W.genericPoint B S hS Y) hdecY V
    have hcong : Ideal.map (V.scheme.left.1.presheaf.stalkCongr (.of_eq hj₀.symm)).hom.hom
        (maximalIdeal (V.scheme.left.1.presheaf.stalk V.point)) =
        maximalIdeal (V.scheme.left.1.presheaf.stalk (j₀.left.1 U₀.point)) :=
      map_maximalIdeal_of_iso _
    have hid : Ideal.map φ (maximalIdeal ↥(W.genericHenselianLocalRing B S hS hY hdecY)) =
        Ideal.map (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U₀)
          (Ideal.map (j₀.left.1.stalkMap U₀.point).hom
            (maximalIdeal (V.scheme.left.1.presheaf.stalk (j₀.left.1 U₀.point)))) := by
      rw [← hmaxV, ← hcong, Ideal.map_map, Ideal.map_map, Ideal.map_map]
      congr 1
      ext a
      exact hcompat₀ a
    rw [primeDivisorFlatMultiplicity, hid,
      length_baseChange_eq_of_map_maximalIdeal _ _ hmaxU,
      length_baseChange_quotient_eq
        (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U₀)]

/-- Multiplying two finite elements of `ℕ∞` by a common factor which keeps both finite multiplies
their difference: if the factor is infinite both elements are zero. -/
private theorem natCast_toNat_mul_sub_toNat_mul (L x y : ℕ∞) (hx : x ≠ ⊤) (hy : y ≠ ⊤)
    (hLx : L * x ≠ ⊤) (hLy : L * y ≠ ⊤) :
    (((L * x).toNat : ℕ) : ℤ) - ((L * y).toNat : ℤ) =
      (L.toNat : ℤ) * ((x.toNat : ℤ) - (y.toNat : ℤ)) := by
  by_cases hL : L = ⊤
  · subst hL
    obtain rfl : x = 0 := not_not.mp fun h => hLx (ENat.top_mul h)
    obtain rfl : y = 0 := not_not.mp fun h => hLy (ENat.top_mul h)
    simp
  · lift L to ℕ using hL
    lift x to ℕ using hx
    lift y to ℕ using hy
    simp only [← ENat.coe_mul, ENat.toNat_coe]
    push_cast
    ring

/-- Equal presentations of a unit of a total ring of fractions by nonzerodivisors give the same
difference of orders of vanishing. -/
private theorem toNat_ord_sub_eq_of_mk'_eq {R : Type*} [CommRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Nontrivial R] (K : Type*) [CommRing K] [Algebra R K]
    [IsFractionRing R K] (a b c d : R⁰)
    (h : IsLocalization.mk' K (a : R) b = IsLocalization.mk' K (c : R) d) :
    ((Ring.ord R (a : R)).toNat : ℤ) - (Ring.ord R (b : R)).toNat =
      (Ring.ord R (c : R)).toNat - (Ring.ord R (d : R)).toNat := by
  have hu1 := Ring.isUnit_mk'_of_mem (K := K) _ a.2 b
  have hu2 := Ring.isUnit_mk'_of_mem (K := K) _ c.2 d
  rw [← Ring.ordTotalFracInt_mk' R a b hu1, ← Ring.ordTotalFracInt_mk' R c d hu2]
  exact Ring.ordTotalFracInt_congr R hu1 hu2 h

include hintY in
/-- **The order of vanishing of the reading of a rational function along a flat morphism, at a
prime divisor lying over a prime divisor** (Stacks 02M1 at the henselian local rings). In the
situation of
`PrimeDivisor.exists_henselianLocalRingHom_rationalFunctionsToGenericTotalFractionRingOfFlat`
there is a square of elementary étale neighbourhoods `j : U → V` over `f`, of `ξ` and of `η`,
such that for every `g ∈ R(Y)^*` and every presentation `a / b` by nonzerodivisors of the
reading of `g` in `Q(𝒪^h_{X, ξ})`,

  `ord(a) - ord(b) = m · ord_W(g)`,

`m` being the colength of `𝔪_{V, v} 𝒪_{U, u}` and `ord_W` the order of vanishing of Stacks
0ENL. -/
theorem PrimeDivisor.exists_natCast_ord_sub_eq_length_mul_ordRationalFunction
    (hZ : pointsMap B S hS X f (Z.genericPoint B S hS X) = W.genericPoint B S hS Y) :
    ∃ (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))
      (V : ElementaryEtaleNeighborhood B S hS Y hY (W.genericPoint B S hS Y))
      (j : U.scheme ⟶ V.scheme),
      yoneda.map j ≫ V.toSpace = U.toSpace ≫ f ∧
      ∀ (g : (rationalFunctions B S hS hY)ˣ)
        (a b : (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰),
        IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
            (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) b =
          Z.rationalFunctionsToGenericTotalFractionRingOfFlat B S hS hX hdec hN hY hintY f hf
            (g : rationalFunctions B S hS hY) →
        letI : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
          henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
        ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
              (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec))).toNat : ℤ) -
            ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
              (b : ↥(Z.genericHenselianLocalRing B S hS hX hdec))).toNat : ℤ) =
          ((Module.length (U.scheme.left.1.presheaf.stalk U.point)
            (U.scheme.left.1.presheaf.stalk U.point ⧸
              Ideal.map (j.left.1.stalkMap U.point).hom
                (maximalIdeal (V.scheme.left.1.presheaf.stalk (j.left.1 U.point))))).toNat :
            ℤ) * ordRationalFunction B S hS hY hintY hNY g W := by
  let := henselianLocalRing_isLocalRing B S hS Y hY (W.genericPoint B S hS Y) hintY.isDecentSpace
  let : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  obtain ⟨hdimB, hnoethB⟩ :=
    PrimeDivisor.ringKrullDim_eq_one_and_isNoetherianRing_genericHenselianLocalRing B S hS hX
      hdec hN Z
  let := hnoethB
  let : Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    Ring.krullDimLE_iff.mpr (by rw [hdimB]; norm_num)
  obtain ⟨hdimA, hnoethA⟩ :=
    PrimeDivisor.ringKrullDim_eq_one_and_isNoetherianRing_genericHenselianLocalRing B S hS hY
      hintY.isDecentSpace hNY W
  let := hnoethA
  let : Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hY hintY.isDecentSpace) :=
    Ring.krullDimLE_iff.mpr (by rw [hdimA]; norm_num)
  obtain ⟨φ, hφloc, hφflat, hnat, U, V, j, hsq, hlen⟩ :=
    Z.exists_henselianLocalRingHom_rationalFunctionsToGenericTotalFractionRingOfFlat B S hS hX
      hdec hN hY hintY.isDecentSpace hintY hNY W f hf hZ
  refine ⟨U, V, j, hsq, fun g a b hab => ?_⟩
  have hgu : IsUnit (W.rationalFunctionsToGenericTotalFractionRing B S hS hY hintY.isDecentSpace
      hintY hNY (g : rationalFunctions B S hS hY)) := g.isUnit.map _
  obtain ⟨a', b', hab'⟩ := Ring.exists_mk'_of_isUnit
    (A := ↥(W.genericHenselianLocalRing B S hS hY hintY.isDecentSpace))
    (W.genericTotalFractionRing B S hS hY hintY.isDecentSpace) hgu
  have hφa : φ (a' : ↥(W.genericHenselianLocalRing B S hS hY hintY.isDecentSpace)) ∈
      (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰ :=
    Ring.map_mem_nonZeroDivisors_of_flatHom hφflat a'.2
  have hφb : φ (b' : ↥(W.genericHenselianLocalRing B S hS hY hintY.isDecentSpace)) ∈
      (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰ :=
    Ring.map_mem_nonZeroDivisors_of_flatHom hφflat b'.2
  have hread : IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
      (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) b =
      IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
        ((⟨_, hφa⟩ : (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰) :
          ↥(Z.genericHenselianLocalRing B S hS hX hdec)) ⟨_, hφb⟩ := by
    rw [hab, hnat g, hab']
    exact IsLocalization.map_mk' _ _ _
  rw [toNat_ord_sub_eq_of_mk'_eq (Z.genericTotalFractionRing B S hS hX hdec) a b ⟨_, hφa⟩ ⟨_, hφb⟩
    hread, ordRationalFunction_eq_length_sub_length B S hS hY hintY hNY g W a' b' hab',
    ← hlen]
  show (((Ring.ord _ (φ (a' : ↥(W.genericHenselianLocalRing B S hS hY
      hintY.isDecentSpace)))).toNat : ℕ) : ℤ) -
    ((Ring.ord _ (φ (b' : ↥(W.genericHenselianLocalRing B S hS hY
      hintY.isDecentSpace)))).toNat : ℤ) = _
  rw [Ring.ord_map_of_flatHom hφloc hφflat, Ring.ord_map_of_flatHom hφloc hφflat]
  refine natCast_toNat_mul_sub_toNat_mul _ _ _ (Ring.ord_ne_top a'.2) (Ring.ord_ne_top b'.2)
    ?_ ?_
  · rw [← Ring.ord_map_of_flatHom hφloc hφflat]; exact Ring.ord_ne_top hφa
  · rw [← Ring.ord_map_of_flatHom hφloc hφflat]; exact Ring.ord_ne_top hφb

/-- A unit has order of vanishing zero: the quotient by the ideal it generates is zero. -/
private theorem ord_eq_zero_of_isUnit {A : Type*} [CommRing A] {u : A} (hu : IsUnit u) :
    Ring.ord A u = 0 := by
  have hspan : Ideal.span {u} = ⊤ := Ideal.span_singleton_eq_top.mpr hu
  rw [Ring.ord, hspan]
  have : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Module.length_eq_zero

include hintY hNY in
/-- **Over the generic point of `Y` the reading of a rational function has order zero.** In the
situation of
`PrimeDivisor.exists_henselianLocalRingHom_rationalFunctionsToGenericTotalFractionRingOfFlat`,
suppose instead that the generic point `ξ` of `Z` lies over the generic point of `Y`. Then for
every `g ∈ R(Y)^*` and every presentation `a / b` by nonzerodivisors of the reading of `g` in
`Q(𝒪^h_{X, ξ})`, `ord(a) = ord(b)`. -/
theorem PrimeDivisor.natCast_ord_sub_eq_zero_of_pointsMap_eq_genericPoint
    (hZ : pointsMap B S hS X f (Z.genericPoint B S hS X) =
      _root_.AlgebraicGeometry.Space.genericPoint B S hS hY hintY)
    (g : (rationalFunctions B S hS hY)ˣ)
    (a b : (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰)
    (hab : IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
        (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) b =
      Z.rationalFunctionsToGenericTotalFractionRingOfFlat B S hS hX hdec hN hY hintY f hf
        (g : rationalFunctions B S hS hY)) :
    letI : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
      henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec))).toNat : ℤ) -
        ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (b : ↥(Z.genericHenselianLocalRing B S hS hX hdec))).toNat : ℤ) = 0 := by
  let : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  obtain ⟨hdimB, hnoethB⟩ :=
    PrimeDivisor.ringKrullDim_eq_one_and_isNoetherianRing_genericHenselianLocalRing B S hS hX
      hdec hN Z
  let := hnoethB
  let : Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    Ring.krullDimLE_iff.mpr (by rw [hdimB]; norm_num)
  have key := exists_henselianLocalRingHom_affineChartSquare B S hS hX hdec hY hintY.isDecentSpace
    f (Z.genericPoint B S hS X)
  obtain ⟨V, U₀, j₀, hj₀, φ, hsq₀, hVaff, hφloc, hcompat₀, -⟩ := key
  obtain ⟨U, r, hUaff⟩ := ElementaryEtaleNeighborhood.exists_affine_refinement B S hS X hX
    (Z.genericPoint B S hS X) U₀
  have : IsAffine V.scheme.left.1 := hVaff
  have : IsAffine U.scheme.left.1 := hUaff
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.scheme) := hUaff
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.scheme) := hVaff
  have := Z.isLocallyNoetherian_chart B S hS hX hN U
  have hVN : IsLocallyNoetherian V.scheme.left.1 :=
    (exists_atlas_iff_forall_etale B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T) hY).mp
      hNY V.scheme V.toSpace (ElementaryEtaleNeighborhood.presheaf_etale_toSpace B S hS hY V)
  have hsq : yoneda.map (r.hom ≫ j₀) ≫ V.toSpace = U.toSpace ≫ f := by
    rw [Functor.map_comp, Category.assoc, hsq₀, ← Category.assoc, r.over]
  have hj := nonZeroDivisors_le_comap_of_isFlat_square B S hS hX hY f hf U V (r.hom ≫ j₀) hsq
  have hηgen : _root_.AlgebraicGeometry.Space.genericPoint B S hS hY hintY ∈
      genericPoints (points B S hS Y) := by
    have : IrreducibleSpace (points B S hS Y) := hintY.2.2
    show closure {_root_.AlgebraicGeometry.Space.genericPoint B S hS hY hintY} ∈
      irreducibleComponents (points B S hS Y)
    rw [(_root_.AlgebraicGeometry.Space.isGenericPoint_genericPoint B S hS hY hintY).def]
    exact ⟨IrreducibleSpace.isIrreducible_univ _, fun _ _ _ => Set.subset_univ _⟩
  have hdim0 := (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hY hintY.isDecentSpace
    _).mp hηgen
  have hvgen : V.point ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj V.scheme) := by
    have h := mem_genericPoints_of_pointsMap_eq B S hS hY V.scheme V.toSpace V.etale_toSpace
      (hZ ▸ hdim0) _ V.map_point
    rwa [pointsToScheme_presheafPoint] at h
  have hunit : ∀ x ∈ (Γ(V.scheme.left.1, ⊤))⁰,
      IsUnit (Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U
        (chartGlobalSectionsRestrict B S hS (r.hom ≫ j₀) x)) := by
    intro x hx
    have hgx : IsUnit (V.scheme.left.1.presheaf.germ ⊤ V.point trivial x) :=
      Stacks.AlgebraicGeometry.GenericPointSheaf.isUnit_of_mem_nonZeroDivisors_stalk hvgen
        (V.scheme.left.1.nonZeroDivisors_le_comap_germ_top V.point hx)
    rw [← map_stalkToHenselianLocalRing_germ_eq_neighborhoodSections B S hS hX hdec Z hY _ j₀ hj₀
      r φ hcompat₀ x]
    exact (hgx.map _).map φ
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.mk'_surjective (Γ(V.scheme.left.1, ⊤))⁰
    (rationalFunctionsToTotalFractionRingOfFlat B S hS hY hintY V.scheme V.toSpace
      (isFlat_of_isEtale B S hS V.etale_toSpace) (g : rationalFunctions B S hS hY))
  replace hst : IsLocalization.mk' (FractionRing Γ(V.scheme.left.1, ⊤)) s t =
      rationalFunctionsToTotalFractionRingOfFlat B S hS hY hintY V.scheme V.toSpace
        (isFlat_of_isEtale B S hS V.etale_toSpace) (g : rationalFunctions B S hS hY) := hst
  have hs : s ∈ (Γ(V.scheme.left.1, ⊤))⁰ := by
    refine Stacks.Chow.mem_nonZeroDivisors_of_isUnit_algebraMap
      (Q := FractionRing Γ(V.scheme.left.1, ⊤)) ?_
    rw [← IsLocalization.mk'_spec (FractionRing Γ(V.scheme.left.1, ⊤)) s t, hst]
    exact (g.isUnit.map _).mul (IsLocalization.map_units _ t)
  have hCofX := ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS X hX
    (Z.genericPoint B S hS X) ⟨Z.genericChart B S hS hX hdec⟩
  have hread : Z.rationalFunctionsToGenericTotalFractionRingOfFlat B S hS hX hdec hN hY hintY f hf
      (g : rationalFunctions B S hS hY) =
      IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
        (Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U
          (chartGlobalSectionsRestrict B S hS (r.hom ≫ j₀) s))
        ⟨_, (hunit _ t.2).mem_nonZeroDivisors⟩ := by
    rw [Z.rationalFunctionsToGenericTotalFractionRingOfFlat_eq_neighborhood B S hS hX hdec hN
        hY hintY f hf U _, neighborhoodFlatReading,
      rationalFunctionsToTotalFractionRingOfFlat_comp B S hS hY hintY (U.toSpace ≫ f) _
        V.toSpace (isFlat_of_isEtale B S hS V.etale_toSpace) (r.hom ≫ j₀) hsq hj _, ← hst]
    simp only [chartFractionMap, PrimeDivisor.neighborhoodTotalFractionRingToGeneric,
      IsLocalization.map_mk']
  rw [toNat_ord_sub_eq_of_mk'_eq (Z.genericTotalFractionRing B S hS hX hdec) a b
    ⟨_, (hunit _ hs).mem_nonZeroDivisors⟩ ⟨_, (hunit _ t.2).mem_nonZeroDivisors⟩
    (hab.trans hread)]
  show (((Ring.ord _ (Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U
      (chartGlobalSectionsRestrict B S hS (r.hom ≫ j₀) s))).toNat : ℕ) : ℤ) -
    ((Ring.ord _ (Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U
      (chartGlobalSectionsRestrict B S hS (r.hom ≫ j₀) (t : Γ(V.scheme.left.1, ⊤))))).toNat :
        ℤ) = 0
  rw [ord_eq_zero_of_isUnit (hunit _ hs), ord_eq_zero_of_isUnit (hunit _ t.2)]
  simp

end Square

end Neighborhood

end AlgebraicGeometry.Space

end
