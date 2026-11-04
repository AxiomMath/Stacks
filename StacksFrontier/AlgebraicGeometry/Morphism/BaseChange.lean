module

public import StacksFrontier.AlgebraicGeometry.Morphism.ChartSquare
public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.SectionIso
public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.ChartTwist
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.BaseChangeCompAlgebra

/-!
# The data of Tag 07ZG are compatible with base change

Let `ψ : A ⟶ B` be a homomorphism of quasi-coherent graded `𝒪_S`-algebras and `g : S' ⟶ S` a
morphism of schemes. Write `c : Proj_{S'}(g^*A) ⟶ Proj_S(A)` and
`c' : Proj_{S'}(g^*B) ⟶ Proj_S(B)` for the base-change morphisms of Tag 01O3. Then the open of
Tag 07ZG of the pulled-back homomorphism `g^*ψ : g^*A ⟶ g^*B` is the inverse image of the open of
`ψ`, `U(g^*ψ) = c'^{-1}(U(ψ))`, and `c ∘ r_{g^*ψ} = r_ψ ∘ c'|_{U(g^*ψ)}`.

The comparison is made on the charts over the affine opens `V'` of `S'` carried by `g` into an
affine open `V` of `S`, where both base-change morphisms are `Proj` of the graded ring maps
`Γ(V, -) ⟶ Γ(V', g^*-)` of sections. The one input beyond naturality is that the sections of the
pullback of a quasi-coherent module over `V'` are generated, over the functions on `V'`, by the
pullbacks of the sections over `V` (`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`), so
that precomposing with the graded ring map of sections does not change a domain of definition.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.toSituationHom`: a
  homomorphism of graded algebra data, read as a unital homomorphism of sheaves of graded
  algebras.
* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.ofSituationHom`: the
  converse reading.
* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.pullback`: the inverse
  image `g^*ψ`.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.mapDomain_comp_eq_of_mem_span`: precomposition with a
  graded ring map whose image generates every positive degree as an ideal does not change the
  domain of definition.
* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.baseChangeHom_preimage_relativeMapDomain`:
  `c'^{-1}(U(ψ)) = U(g^*ψ)`.
* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.relativeMapHom_pullback_comp_baseChangeHom`:
  `r_{g^*ψ} ≫ c = c'|_{U(g^*ψ)} ≫ r_ψ`.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom

variable {S S' : Scheme.{u}} {A B : SheafGradedAlgebra S}

/-- A homomorphism of graded algebra data, read as a unital homomorphism of the sheaves of graded
algebras of `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra`. -/
def toSituationHom (ψ : SheafGradedAlgebraHom A B) :
    SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A) (situationAlgebra B) where
  app := ψ.app
  map_mul i j U x y := ψ.app_mul i j U.unop x y
  map_one U := ψ.app_one U.unop

/-- The components of `ψ.toSituationHom` are those of `ψ`. -/
@[simp] theorem toSituationHom_app (ψ : SheafGradedAlgebraHom A B) (n : ℤ) :
    ψ.toSituationHom.app n = ψ.app n := rfl

/-- A unital homomorphism of the sheaves of graded algebras of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra`, read as a homomorphism of
graded algebra data. -/
def ofSituationHom
    (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A) (situationAlgebra B)) :
    SheafGradedAlgebraHom A B where
  app := Φ.app
  app_mul i j U x y := Φ.map_mul i j (op U) x y
  app_one U := Φ.map_one (op U)

/-- The components of `ofSituationHom Φ` are those of `Φ`. -/
@[simp] theorem ofSituationHom_app
    (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A) (situationAlgebra B))
    (n : ℤ) : (ofSituationHom Φ).app n = Φ.app n := rfl

/-- **The inverse image `g^*ψ : g^*A ⟶ g^*B` of a homomorphism of graded algebra data**, degreewise
the inverse image of its components. -/
def pullback (ψ : SheafGradedAlgebraHom A B) (g : S' ⟶ S) :
    SheafGradedAlgebraHom (A.pullback g) (B.pullback g) :=
  ofSituationHom (baseAlgebraMapHom g ψ.toSituationHom)

/-- The degree-`n` component of `g^*ψ` is the inverse image along `g` of the degree-`n` component
of `ψ`. -/
theorem pullback_app (ψ : SheafGradedAlgebraHom A B) (g : S' ⟶ S) (n : ℤ) :
    (ψ.pullback g).app n = (Scheme.Modules.pullback g).map (ψ.app n) := rfl

end Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom

namespace Stacks.AlgebraicGeometry.Tag07ZGMorphism

/-! ### A generation criterion for domains of definition -/

section Algebraic

variable {A₁ A₂ B : Type u} {σ₁ σ₂ τ : Type u}
  [CommRing A₁] [CommRing A₂] [CommRing B]
  [SetLike σ₁ A₁] [AddSubgroupClass σ₁ A₁] [SetLike σ₂ A₂] [AddSubgroupClass σ₂ A₂]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜₁ : ℕ → σ₁) (𝒜₂ : ℕ → σ₂) (ℬ : ℕ → τ) [GradedRing 𝒜₁] [GradedRing 𝒜₂] [GradedRing ℬ]

omit [AddSubgroupClass σ₁ A₁] [GradedRing 𝒜₁] [AddSubgroupClass σ₂ A₂] [GradedRing 𝒜₂] in
/-- **Precomposition with a graded ring map whose image generates every positive degree does not
change the domain of definition.** If every homogeneous element of positive degree `k` of `𝒜₂`
lies in the ideal generated by the image of the degree-`k` part of `𝒜₁`, then
`U(ψ ∘ ρ) = U(ψ)`. -/
theorem mapDomain_comp_eq_of_mem_span (ρ : 𝒜₁ →+*ᵍ 𝒜₂) (ψ : 𝒜₂ →+*ᵍ ℬ)
    (hgen : ∀ k : ℕ, 0 < k → ∀ a ∈ 𝒜₂ k,
      a ∈ Ideal.span ((fun c => ρ c) '' (𝒜₁ k : Set A₁))) :
    mapDomain 𝒜₁ ℬ (ψ.comp ρ) = mapDomain 𝒜₂ ℬ ψ := by
  refine le_antisymm (mapDomain_comp_le 𝒜₁ 𝒜₂ ℬ ρ ψ) fun z hz => ?_
  obtain ⟨k, a, hk, ha, haz⟩ := (mem_mapDomain_iff 𝒜₂ ℬ ψ z).mp hz
  refine (mem_mapDomain_iff 𝒜₁ ℬ (ψ.comp ρ) z).mpr ?_
  by_contra hcon
  have hle : Ideal.span ((fun c => ρ c) '' (𝒜₁ k : Set A₁)) ≤
      Ideal.comap ψ.toRingHom (z : ProjectiveSpectrum ℬ).asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨c, hc, rfl⟩
    by_contra hn
    exact hcon ⟨k, c, hk, hc, hn⟩
  exact haz (hle (hgen k hk a ha))

end Algebraic

/-! ### The graded ring maps of sections of a base change -/

variable {S S' : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)
  (g : S' ⟶ S)

/-- **The square of graded ring maps of sections commutes**: pulling sections back along `g` and
applying `ψ` can be done in either order. -/
theorem sectionBaseChange_comp_sectionHom (U : S.AffineZariskiSite) (U' : S'.AffineZariskiSite)
    (h : U'.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    (sectionBaseChange B g U U' h).comp (ψ.sectionHom U.toOpens) =
      ((ψ.pullback g).sectionHom U'.toOpens).comp (sectionBaseChange A g U U' h) := by
  refine GradedRingHom.ext fun x => ?_
  rw [GradedRingHom.comp_apply, GradedRingHom.comp_apply]
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | of n y =>
    rw [ψ.sectionHom_of U.toOpens y, sectionBaseChange_of, sectionBaseChange_of]
    refine Eq.trans ?_ ((ψ.pullback g).sectionHom_of U'.toOpens _).symm
    congr 1
    exact (Scheme.Modules.pullbackSection_naturality g (ψ.app (n : ℤ)) U.toOpens U'.toOpens h
      y).symm
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- **Induction along a morphism out of an extension of scalars**: a property of the values of
`e : S ⊗_R M ⟶ N` closed under sums and holding at `0` holds everywhere once it holds at the images
of the pure tensors. -/
theorem extendScalars_hom_induction {R S : CommRingCat.{u}} (φ : R ⟶ S) {M : ModuleCat.{u} R}
    {N : ModuleCat.{u} S} (e : (ModuleCat.extendScalars φ.hom).obj M ⟶ N) (P : N → Prop)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (htmul : ∀ (t : S) (m : M), P (e (t ⊗ₜ[R,φ.hom] m)))
    (x : (ModuleCat.extendScalars φ.hom).obj M) : P (e x) := by
  let := φ.hom.toAlgebra
  induction x using TensorProduct.induction_on with
  | zero => exact (congrArg P (e.hom.map_zero)).mpr h0
  | tmul t m => exact htmul t m
  | add x y hx hy => exact (congrArg P (e.hom.map_add x y)).mpr (hadd _ _ hx hy)

/-- **Induction over the sections of the pullback of a quasi-coherent module over an affine
open**: for affine opens `V ⊆ f⁻¹U` the sections of `f^*F` over `V` are sums of functions on `V`
times pullbacks of sections of `F` over `U`
(`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`), so a property closed under sums which
holds at `0` and at those products holds everywhere. -/
theorem pullbackSection_induction {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (P : Γ((Scheme.Modules.pullback f).obj F, V) → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (t : Γ(Y, V)) (a : Γ(F, U)),
      P (t • (show Γ((Scheme.Modules.pullback f).obj F, V) from
        Scheme.Modules.pullbackSection f F U V hVU a)))
    (s : Γ((Scheme.Modules.pullback f).obj F, V)) : P s := by
  have hs : s = (affinePullbackSectionsBaseChangeIso f F hU hV hVU).hom
      ((affinePullbackSectionsBaseChangeIso f F hU hV hVU).inv s) :=
    (Iso.inv_hom_id_apply (affinePullbackSectionsBaseChangeIso f F hU hV hVU) s).symm
  rw [hs]
  refine extendScalars_hom_induction (f.appLE U V hVU)
    (affinePullbackSectionsBaseChangeIso f F hU hV hVU).hom P h0 hadd (fun t m => ?_) _
  rw [affinePullbackSectionsBaseChangeIso_tmul, affinePullbackSectionsBaseChangeIso_one_tmul]
  exact hsmul t m

/-- **The sections of `g^*A` over `U'` are generated by the pullbacks of the sections of `A` over
`U`**, for affine opens `U' ⊆ g⁻¹U`: every homogeneous section of degree `k` lies in the ideal of
the section ring generated by the image of the graded ring map of sections in degree `k`. -/
theorem mem_span_sectionBaseChange (U : S.AffineZariskiSite) (U' : S'.AffineZariskiSite)
    (h : U'.toOpens ≤ g ⁻¹ᵁ U.toOpens) (k : ℕ)
    (a : (A.pullback g).sectionRing U'.toOpens)
    (ha : a ∈ (A.pullback g).grading U'.toOpens k) :
    a ∈ Ideal.span ((fun c => sectionBaseChange A g U U' h c) ''
      ((A.grading U.toOpens k : Set (A.sectionRing U.toOpens)))) := by
  obtain ⟨y, rfl⟩ := ((A.pullback g).mem_grading_iff U'.toOpens a).1 ha
  have := A.isQuasicoherent (k : ℤ)
  set I := Ideal.span ((fun c => sectionBaseChange A g U U' h c) ''
    ((A.grading U.toOpens k : Set (A.sectionRing U.toOpens))))
  refine pullbackSection_induction g (A.piece (k : ℤ)) (U := U.toOpens) U.2 (V := U'.toOpens) U'.2
    h (fun s => DirectSum.of ((A.pullback g).sectionPieces U'.toOpens) k s ∈ I) ?_ ?_ ?_ y
  · exact (congrArg (· ∈ I) (DirectSum.of _ k).map_zero).mpr I.zero_mem
  · intro x y hx hy
    exact (congrArg (· ∈ I) ((DirectSum.of _ k).map_add x y)).mpr (I.add_mem hx hy)
  · intro t m
    have hm := (A.pullback g).strHom_mul_of U'.toOpens t
      (Scheme.Modules.pullbackSection g (A.piece (k : ℤ)) U.toOpens U'.toOpens h m)
    refine hm ▸ I.mul_mem_left _ (Ideal.subset_span ?_)
    exact ⟨_, A.of_mem_grading U.toOpens m, sectionBaseChange_of A g U U' h k m⟩

/-! ### The chart squares of the base-change morphisms -/

/-- **The chart square of the base-change morphisms of Tag 01O3** over an affine open `V'` of `S'`
carried by `g` into an affine open `V` of `S`. -/
def baseChangeChartSquare (V : S.Opens) (hV : IsAffineOpen V) (V' : S'.Opens)
    (hV' : IsAffineOpen V') (h : V' ≤ g ⁻¹ᵁ V) :
    ChartSquare ψ (ψ.pullback g) (baseChangeHom A g) (baseChangeHom B g) V' hV' where
  W := V
  hW := hV
  σA := sectionBaseChange A g ⟨V, hV⟩ ⟨V', hV'⟩ h
  σB := sectionBaseChange B g ⟨V, hV⟩ ⟨V', hV'⟩ h
  hσA := irrelevant_le_map_sectionBaseChange A g ⟨V, hV⟩ ⟨V', hV'⟩ h
  hσB := irrelevant_le_map_sectionBaseChange B g ⟨V, hV⟩ ⟨V', hV'⟩ h
  chart_cA := chart_baseChangeHom A g ⟨V, hV⟩ ⟨V', hV'⟩ h
  chart_cB := chart_baseChangeHom B g ⟨V, hV⟩ ⟨V', hV'⟩ h
  comm := sectionBaseChange_comp_sectionHom ψ g ⟨V, hV⟩ ⟨V', hV'⟩ h
  mapDomain_comp := mapDomain_comp_eq_of_mem_span _ _ _ _ _ fun k _ a ha =>
    mem_span_sectionBaseChange g ⟨V, hV⟩ ⟨V', hV'⟩ h k a ha

/-- The affine opens of `S'` carried by `g` into an affine open of `S` cover `S'`, with their chart
squares. -/
theorem exists_baseChangeChartSquare (y : S') :
    ∃ (V' : S'.Opens) (hV' : IsAffineOpen V'), y ∈ V' ∧
      Nonempty (ChartSquare ψ (ψ.pullback g) (baseChangeHom A g) (baseChangeHom B g) V' hV') := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.base y)) isOpen_univ
  obtain ⟨_, ⟨V', hV', rfl⟩, hyV', hV'V⟩ :=
    S'.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ g ⁻¹ᵁ V from hyV)
      (g ⁻¹ᵁ V).isOpen
  exact ⟨V', hV', hyV', ⟨baseChangeChartSquare ψ g V hV V' hV' hV'V⟩⟩

/-- **The open of Tag 07ZG is compatible with base change**: for `g : S' ⟶ S` the open of the
pulled-back homomorphism `g^*ψ` is the inverse image of the open of `ψ` under the base-change
morphism `Proj_{S'}(g^*B) ⟶ Proj_S(B)` of Tag 01O3. -/
theorem baseChangeHom_preimage_relativeMapDomain :
    baseChangeHom B g ⁻¹ᵁ ψ.relativeMapDomain = (ψ.pullback g).relativeMapDomain :=
  preimage_relativeMapDomain_of_chartSquare (exists_baseChangeChartSquare ψ g)

/-- **The morphism of Tag 07ZG is compatible with base change**: `r_{g^*ψ}` followed by the
base-change morphism `Proj_{S'}(g^*A) ⟶ Proj_S(A)` is the restriction of the base-change morphism
`Proj_{S'}(g^*B) ⟶ Proj_S(B)` to `U(g^*ψ)` followed by `r_ψ`. -/
theorem relativeMapHom_pullback_comp_baseChangeHom :
    relativeMapHom (ψ.pullback g) ≫ baseChangeHom A g =
      (baseChangeHom B g).resLE ψ.relativeMapDomain (ψ.pullback g).relativeMapDomain
          (baseChangeHom_preimage_relativeMapDomain ψ g).ge ≫ relativeMapHom ψ :=
  relativeMapHom_comp_of_chartSquare (exists_baseChangeChartSquare ψ g)

end Stacks.AlgebraicGeometry.Tag07ZGMorphism

end
