module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.BaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Properties.Normal

/-!
# Extending a Galois cover of the generic fibre over a Noetherian base: the induction

Let `f : X ⟶ S` be a morphism to an integral scheme with generic point `η`, and `Z ⟶ X_η` a
finite étale Galois cover with group `G`. Say that `Z` *extends over* an open `U ∋ η` if there is
a finite étale Galois cover of `f⁻¹(U)` with group `G` whose restriction to `X_η` is `Z`,
equivariantly. If `S` is a Noetherian space, `Z` extends over some open, and every proper open
over which `Z` extends is contained in a strictly larger one, then `Z` extends over `S`. This is
the maximal-open argument in the proof of [Stacks, Tag 0EYJ].

## Main definitions

* `AlgebraicGeometry.Abhyankar.GaloisExtendsOver`: the predicate that `Z` extends over an open.

## Main results

* `AlgebraicGeometry.Abhyankar.galoisExtendsOver_top`: on a Noetherian base, `Z` extends over `S`
  if it extends over some open and every proper such open lies in a strictly larger one.
* `AlgebraicGeometry.Abhyankar.exists_of_galoisExtendsOver_top`: extending over all of `S`
  extends over `X`.

The assembly of [Stacks, Tag 0EYJ] from this induction is in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.GaloisCoverNoetherian`.

## References

* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Abhyankar

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsIntegral S]

/-- The generic fibre `X_η` maps into `f⁻¹(U)` for every open `U ∋ η`. -/
def genericFiberToPreimage (U : S.Opens) (hη : genericPoint S ∈ U) :
    f.fiber (genericPoint S) ⟶ (f ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (f ⁻¹ᵁ U).ι (f.fiberι (genericPoint S)) (by
    rw [Scheme.Hom.range_fiberι, Scheme.Opens.range_ι]
    rintro x hx
    change f x ∈ U
    rw [show f x = genericPoint S from hx]
    exact hη)

/-- The map `X_η ⟶ f⁻¹(U)` followed by the inclusion `f⁻¹(U) ⟶ X` is the inclusion of the
generic fibre `X_η ⟶ X`. -/
@[reassoc (attr := simp)]
lemma genericFiberToPreimage_ι (U : S.Opens) (hη : genericPoint S ∈ U) :
    genericFiberToPreimage f U hη ≫ (f ⁻¹ᵁ U).ι = f.fiberι (genericPoint S) :=
  IsOpenImmersion.lift_fac _ _ _

variable {G : Type v} [Group G] [Finite G] (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)

/-- `Z` extends over the open `U`: there is a finite étale Galois cover of `f⁻¹(U)` with group `G`
whose restriction to the generic fibre is `Z`, equivariantly. -/
def GaloisExtendsOver (U : S.Opens) : Prop :=
  ∃ (hη : genericPoint S ∈ U) (Y : FiniteEtaleGaloisCover (f ⁻¹ᵁ U).toScheme G)
    (e : (finiteEtaleBaseChange (genericFiberToPreimage f U hη)).obj Y.obj ≅ Z.obj),
    ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange (genericFiberToPreimage f U hη)).map (Y.action g).asIso.hom ≫
      e.hom = e.hom ≫ (Z.action g).asIso.hom

/-- **The maximal-open argument.** On a Noetherian space, if `Z` extends over some open and every
proper open over which it extends lies in a strictly larger one, then `Z` extends over `S`. -/
theorem galoisExtendsOver_top [TopologicalSpace.NoetherianSpace S]
    (h₀ : ∃ U, GaloisExtendsOver f Z U)
    (hstep : ∀ U, GaloisExtendsOver f Z U → U ≠ ⊤ → ∃ U', U < U' ∧ GaloisExtendsOver f Z U') :
    GaloisExtendsOver f Z ⊤ := by
  obtain ⟨U₀, hU₀⟩ := h₀
  obtain ⟨U, hU, hmax⟩ := (wellFounded_gt (α := S.Opens)).has_min
    {U | GaloisExtendsOver f Z U} ⟨U₀, hU₀⟩
  by_cases htop : U = ⊤
  · exact htop ▸ hU
  · obtain ⟨U', hUU', hU'⟩ := hstep U hU htop
    exact absurd hUU' (hmax U' hU')

/-- Extending over all of `S` extends over `X`. -/
theorem exists_of_galoisExtendsOver_top (h : GaloisExtendsOver f Z ⊤) :
    ∃ (Y : FiniteEtaleGaloisCover X G)
      (e : (finiteEtaleBaseChange (f.fiberι (genericPoint S))).obj Y.obj ≅ Z.obj),
      ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange (f.fiberι (genericPoint S))).map (Y.action g).asIso.hom ≫
        e.hom = e.hom ≫ (Z.action g).asIso.hom := by
  obtain ⟨hη, Y, e, he⟩ := h
  let θ : X ⟶ (f ⁻¹ᵁ ⊤).toScheme := X.topIso.inv
  have : IsIso θ := ⟨⟨X.topIso.hom, X.topIso.inv_hom_id, X.topIso.hom_inv_id⟩⟩
  have : ConnectedSpace ((𝟭 Scheme).obj Y.obj.left) := Y.connected
  have hconn : ConnectedSpace ((finiteEtaleBaseChange θ).obj Y.obj).left :=
    (asIso (pullback.fst Y.obj.hom θ)).hom.homeomorph.symm.surjective.connectedSpace
      (asIso (pullback.fst Y.obj.hom θ)).hom.homeomorph.symm.continuous
  have hfac : genericFiberToPreimage f ⊤ hη = f.fiberι (genericPoint S) ≫ θ := by
    rw [← cancel_mono (f ⁻¹ᵁ ⊤).ι, genericFiberToPreimage_ι, Category.assoc]
    exact (Category.comp_id _).symm.trans (congrArg _ (Scheme.toIso_inv_ι X).symm)
  let c := finiteEtaleBaseChangeComp (f.fiberι (genericPoint S)) θ _ hfac
  refine ⟨Y.baseChange θ hconn, (c.app Y.obj).symm ≪≫ e, fun g ↦ ?_⟩
  have hnat := c.inv.naturality (Y.action g).asIso.hom
  simp only [Functor.comp_map] at hnat
  change (finiteEtaleBaseChange (f.fiberι (genericPoint S))).map
      ((finiteEtaleBaseChange θ).map (Y.action g).asIso.hom) ≫ c.inv.app Y.obj ≫ e.hom = _
  rw [← Category.assoc, hnat, Category.assoc, he]
  rfl

end AlgebraicGeometry.Abhyankar

