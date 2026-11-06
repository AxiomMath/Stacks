module

public import Mathlib.Order.Zorn
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsolutelyQuasiSeparatedAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStageSiteSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrictRepresentable

/-!
# A maximal ideal of non-schematic base change

Let `X` be an algebraic space over an affine scheme `Spec A` whose structure morphism is
quasi-compact and quasi-separated. If `X` is not a scheme then there is an ideal `I ⊂ A`
such that the base change `X_{A/I}` is not a scheme while `X_{A/I'}` is a scheme for every
ideal `I'` strictly containing `I`. This is Stacks 0B81.

## Main definitions

* `AlgebraicGeometry.Space.quotientBase`: `Spec (A/I)` as an object of the big fppf site
  over `Spec A`, through the morphism induced by `A → A/I`.
* `AlgebraicGeometry.Space.quotientSpace`: the base change `X_{A/I} = X ×_{Spec A} Spec A/I`.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_spec_quotient`: a quotient of a ring whose spectrum
  belongs to the site has its spectrum in the site too.
* `AlgebraicGeometry.Space.quotientDescentSituation`: for a directed family of ideals, the
  base changes to the quotients form Situation 084R with limit the base change to the
  quotient by the supremum.
* `AlgebraicGeometry.Space.isRepresentable_quotientSpace_iff`: the fibre product reading and
  the restriction reading of "the base change `X_{A/I}` is a scheme" agree.
* `AlgebraicGeometry.Space.exists_maximal_not_isRepresentable_quotientSpace`:
  **Stacks 0B81**, with nothing assumed beyond the tag's own hypotheses.
* `AlgebraicGeometry.Space.exists_maximal_not_isRepresentable_relocalizeRestrict`: the same, in
  the restriction reading.

## Implementation notes

An algebraic space over `Spec A` is a presheaf on the big fppf site over `Spec A`, and being
a scheme is representability of that presheaf. The base change `X_{A/I}` is formed as the
presheaf fibre product `X ×_{Spec A} Spec (A/I)`, exactly as the base change to a completed
base is formed in `StacksFrontier/AlgebraicGeometry/Spaces/CompletionBaseChange.lean`; `Spec A`
itself is the terminal object `Over.mk (𝟙 _)` of the site, so the structure morphism of `X`
is the unique morphism to it. The other reading of the base change — the restriction of `X`
to the big fppf site over `Spec (A/I)`, which is the base change construction of Stacks 03I5
part (1) — gives the same answer to "is it a scheme", by
`AlgebraicGeometry.Space.isRepresentable_quotientSpace_iff`, and the tag is stated in both
readings.

The source proof is Zorn's lemma applied to the set of ideals `I` with `X_{A/I}` not a
scheme. It contains `(0)` because `Spec (A/0) → Spec A` is an isomorphism and `X` is not a
scheme. For a chain `K` of such ideals, `A/⨆ K` is the filtered colimit of the `A/K i`
(`AlgebraicGeometry.Space.isColimitQuotientRingCocone`), so `Spec (A/⨆ K)` is the limit of
the `Spec (A/K i)` — in schemes because `Spec` is a right adjoint, in the site because the
inclusion of the site into schemes is fully faithful and the limit is already an object of
the site, and in the slice over `Spec A` because `Over.isLimitLiftCone` lifts a limit cone
together with a compatible morphism to the base. Base changing along the structure morphism
of `X` preserves that limit, the index category being connected, so the base changes
`X_{A/K i}` form a limit situation with limit `X_{A/⨆ K}`. Stacks 07SR then makes one stage
a scheme, contradicting membership in the chain.

No size hypothesis on the chain is needed: the limit of the system of site objects is not
constructed, it is exhibited — `Spec (A/⨆ K)` belongs to the site by
`AlgebraicGeometry.BigFppfSite.contains_spec_quotient` — so the general existence result for
limits of affine objects of the site, which does carry a size bound, is never invoked.

*Where Stacks 07SR comes from, and why the Zorn chain needs no bound.* Stacks 07SR is
`AlgebraicGeometry.Space.DescentSituation.exists_isRepresentable_system_obj_of_isSiteSmall`, and
it asks of the inverse system only that it be small for the site,
`AlgebraicGeometry.Space.IsSiteSmall`. The system here meets that condition with nothing asked
of the index: its transition morphisms are closed immersions, because `A/K i ↠ A/K j` is
surjective (`AlgebraicGeometry.Space.isClosedImmersion_quotientSpaceDiagram_map`), hence
monomorphisms, and that is the second alternative of
`AlgebraicGeometry.Space.IsSiteSmall`. So the registration carries no side condition on the
site.

**Why the chain is not thinned.** An earlier form of this argument shrank the chain to a
subfamily with the same supremum, of cardinality at most `#A` and hence below `B.cutoff`, in
order to meet a Stacks 07SR stated at `< B.cutoff.ord.cof`; that needed the cutoff to be
regular, and the two bounds cannot otherwise be made to agree. For `κ = ℶ_{ω₁}`, which
satisfies every condition `AlgebraicGeometry.BigFppfSite` imposes while being singular of
cofinality `ω₁`, take `A = F[x_α : α < ω₁]` over a field `F` and the chain
`I_β = (x_α : α < β)`: every subfamily with the same supremum has cardinality exactly
`ω₁ = cof (κ.ord)`, failing the strict inequality. The monomorphism route used instead needs
no thinning at all.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 0B81](https://stacks.math.columbia.edu/tag/0B81)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### Quotients stay inside the site -/

/-- If the spectrum of a ring `A` is an object of a big fppf site, then so is the spectrum of
every quotient of `A`: the quotient is a surjective image of `A`, so its cardinality is no
larger, and the size of an affine scheme is the cardinality of its ring together with `ℵ₀`. -/
theorem BigFppfSite.contains_spec_quotient (B : BigFppfSite.{u}) {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (.of A))) (I : Ideal A) :
    B.Contains (Spec (.of (A ⧸ I))) :=
  Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hA
    ((Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := I))).trans
      (le_max_right _ _))

namespace Space

/-! ### `A/⨆ I` as a filtered colimit of the `A/I` -/

section RingColimit

variable {A : Type u} [CommRing A] {ι : Type u} [Preorder ι]

/-- The inverse system of quotients `A/K i` of a monotone family of ideals, as a diagram of
commutative rings. -/
noncomputable def quotientRingDiagram (K : ι → Ideal A) (hK : Monotone K) :
    ι ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (A ⧸ K i)
  map f := CommRingCat.ofHom
    (Ideal.Quotient.factor (S := K _) (T := K _) (hK (leOfHom f)))
  map_id i := by
    apply CommRingCat.hom_ext
    change Ideal.Quotient.factor (S := K i) (T := K i) (hK le_rfl) = RingHom.id _
    rw [Ideal.Quotient.factor_eq]
  map_comp f g := by
    apply CommRingCat.hom_ext
    change Ideal.Quotient.factor (S := K _) (T := K _) (hK (leOfHom (f ≫ g))) =
      (Ideal.Quotient.factor (hK (leOfHom g))).comp
        (Ideal.Quotient.factor (hK (leOfHom f)))
    rw [Ideal.Quotient.factor_comp]

/-- The cocone on `AlgebraicGeometry.Space.quotientRingDiagram` with vertex `A/⨆ K`. -/
noncomputable def quotientRingCocone (K : ι → Ideal A) (hK : Monotone K) :
    Cocone (quotientRingDiagram K hK) where
  pt := CommRingCat.of (A ⧸ ⨆ i, K i)
  ι :=
    { app := fun i => CommRingCat.ofHom
        (Ideal.Quotient.factor (S := K i) (T := ⨆ j, K j) (le_iSup K i))
      naturality := by
        intro i j f
        apply CommRingCat.hom_ext
        change (Ideal.Quotient.factor (S := K j) (T := ⨆ k, K k) (le_iSup K j)).comp
            (Ideal.Quotient.factor (S := K i) (T := K j) (hK (leOfHom f))) =
          Ideal.Quotient.factor (S := K i) (T := ⨆ k, K k) (le_iSup K i)
        rw [Ideal.Quotient.factor_comp] }

/-- `A/⨆ K` is the filtered colimit of the `A/K i` along a directed monotone family of
ideals `K`: an element of `⨆ K` already lies in some `K i`, so a compatible family of maps
out of the `A/K i` kills it. -/
@[ega "IV 5.13.1" "Clause (i), special case"]
noncomputable def isColimitQuotientRingCocone [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (K : ι → Ideal A) (hK : Monotone K) :
    IsColimit (quotientRingCocone K hK) := by
  classical
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  have hdir : ∀ i j : ι, ∃ k, i ≤ k ∧ j ≤ k := fun i j => directed_of (· ≤ ·) i j
  have hKdir : Directed (· ≤ ·) K := hK.directed_le
  let lift (c : Cocone (quotientRingDiagram K hK)) : A ⧸ (⨆ i, K i) →+* c.pt :=
    Ideal.Quotient.lift (⨆ i, K i)
      ((c.ι.app i₀).hom.comp (Ideal.Quotient.mk (K i₀))) (by
        intro x hx
        obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed K hKdir).mp hx
        obtain ⟨k, hik, hi₀k⟩ := hdir i i₀
        have hcomp : (c.ι.app k).hom.comp
            (Ideal.Quotient.factor (S := K i₀) (T := K k) (hK hi₀k)) = (c.ι.app i₀).hom :=
          congrArg CommRingCat.Hom.hom (c.w (homOfLE hi₀k))
        have hval := RingHom.congr_fun hcomp (Ideal.Quotient.mk (K i₀) x)
        have hstage : ((c.ι.app i₀).hom.comp (Ideal.Quotient.mk (K i₀))) x =
            (c.ι.app k).hom (Ideal.Quotient.mk (K k) x) := by
          have hval' : (c.ι.app k).hom
              (Ideal.Quotient.factor (S := K i₀) (T := K k) (hK hi₀k)
                (Ideal.Quotient.mk (K i₀) x)) = (c.ι.app i₀).hom
                  (Ideal.Quotient.mk (K i₀) x) := hval
          rw [Ideal.Quotient.factor_mk] at hval'
          exact hval'.symm
        rw [hstage]
        have hz : Ideal.Quotient.mk (K k) x = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr ((hK hik) hi)
        change (c.ι.app k).hom (Ideal.Quotient.mk (K k) x) = 0
        rw [hz]
        exact map_zero _)
  have hlift_stage (c : Cocone (quotientRingDiagram K hK)) (i : ι) :
      (lift c).comp (Ideal.Quotient.factor (S := K i) (T := ⨆ j, K j) (le_iSup K i)) =
        (c.ι.app i).hom := by
    obtain ⟨k, hi₀k, hik⟩ := hdir i₀ i
    have hcomp₀ : (c.ι.app k).hom.comp
        (Ideal.Quotient.factor (S := K i₀) (T := K k) (hK hi₀k)) = (c.ι.app i₀).hom :=
      congrArg CommRingCat.Hom.hom (c.w (homOfLE hi₀k))
    have hcompᵢ : (c.ι.app k).hom.comp
        (Ideal.Quotient.factor (S := K i) (T := K k) (hK hik)) = (c.ι.app i).hom :=
      congrArg CommRingCat.Hom.hom (c.w (homOfLE hik))
    apply RingHom.ext
    intro x
    induction x using Quotient.inductionOn with
    | h a =>
      change lift c ((Ideal.Quotient.factor (S := K i) (T := ⨆ j, K j)
          (le_iSup K i)) (Ideal.Quotient.mk (K i) a)) =
        (c.ι.app i).hom (Ideal.Quotient.mk (K i) a)
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.lift_mk]
      have hleft := RingHom.congr_fun hcomp₀ (Ideal.Quotient.mk (K i₀) a)
      have hright := RingHom.congr_fun hcompᵢ (Ideal.Quotient.mk (K i) a)
      have hleft' : (c.ι.app i₀).hom (Ideal.Quotient.mk (K i₀) a) =
          (c.ι.app k).hom (Ideal.Quotient.mk (K k) a) := by
        have hleftA : (c.ι.app k).hom
            (Ideal.Quotient.factor (S := K i₀) (T := K k) (hK hi₀k)
              (Ideal.Quotient.mk (K i₀) a)) =
            (c.ι.app i₀).hom (Ideal.Quotient.mk (K i₀) a) := hleft
        rw [Ideal.Quotient.factor_mk] at hleftA
        exact hleftA.symm
      have hright' : (c.ι.app k).hom (Ideal.Quotient.mk (K k) a) =
          (c.ι.app i).hom (Ideal.Quotient.mk (K i) a) := by
        have hrightA : (c.ι.app k).hom
            (Ideal.Quotient.factor (S := K i) (T := K k) (hK hik)
              (Ideal.Quotient.mk (K i) a)) =
            (c.ι.app i).hom (Ideal.Quotient.mk (K i) a) := hright
        rw [Ideal.Quotient.factor_mk] at hrightA
        exact hrightA
      exact hleft'.trans hright'
  refine ⟨fun c => CommRingCat.ofHom (lift c), ?_, ?_⟩
  · exact fun c i => CommRingCat.hom_ext (hlift_stage c i)
  · intro c m hm
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    induction x using Quotient.inductionOn with
    | h a =>
      have hstage := congrArg CommRingCat.Hom.hom (hm i₀)
      have heval := RingHom.congr_fun hstage (Ideal.Quotient.mk (K i₀) a)
      have h₁ : m (Ideal.Quotient.mk (⨆ i, K i) a) =
          (c.ι.app i₀).hom (Ideal.Quotient.mk (K i₀) a) := by
        change (m.hom) (Ideal.Quotient.factor (S := K i₀) (T := ⨆ i, K i)
            (le_iSup K i₀) (Ideal.Quotient.mk (K i₀) a)) = _ at heval
        rw [Ideal.Quotient.factor_mk] at heval
        exact heval
      have h₂ : lift c (Ideal.Quotient.mk (⨆ i, K i) a) =
          (c.ι.app i₀).hom (Ideal.Quotient.mk (K i₀) a) := by
        simp only [lift, Ideal.Quotient.lift_mk]
        rfl
      exact h₁.trans h₂.symm

end RingColimit

/-! ### The quotient bases as objects of the site -/

section QuotientBase

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))

/-- The terminal object `Spec A` of the big fppf category over `Spec A`. -/
noncomputable abbrev affineBaseObject : BigFppfOver B (Spec (.of A)) hA :=
  Over.mk (𝟙 (B.obj hA))

/-- `Spec (A/I)` as an object of the big fppf category over `Spec A`, through the morphism
induced by `A → A/I`. -/
noncomputable def quotientBase (I : Ideal A) : BigFppfOver B (Spec (.of A)) hA :=
  siteObject B (Spec (.of A)) hA (B.contains_spec_quotient hA I)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

/-- The underlying scheme of `AlgebraicGeometry.Space.quotientBase` is affine. -/
instance isAffine_quotientBase (I : Ideal A) :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (quotientBase A B hA I)) :=
  inferInstanceAs (IsAffine (Spec (.of (A ⧸ I))))

/-- The underlying scheme of the terminal object `Spec A` is affine. -/
instance isAffine_affineBaseObject :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (affineBaseObject A B hA)) :=
  inferInstanceAs (IsAffine (Spec (.of A)))

/-- The structure morphism `Spec (A/I) ⟶ Spec A` as a morphism of the site over
`Spec A`. -/
noncomputable def quotientBaseHom (I : Ideal A) :
    quotientBase A B hA I ⟶ affineBaseObject A B hA :=
  Over.homMk (quotientBase A B hA I).hom (by simp)

/-- The base change `X_{A/I} = X ×_{Spec A} Spec (A/I)` of a presheaf `X` over `Spec A`
along `Spec (A/I) ⟶ Spec A`. -/
noncomputable def quotientSpace {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (φ : X ⟶ yoneda.obj (affineBaseObject A B hA)) (I : Ideal A) :
    (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u :=
  pullback (yoneda.map (quotientBaseHom A B hA I)) φ

end QuotientBase

/-! ### `Spec (A/⨆ K)` as a limit of the `Spec (A/K i)` in the site -/

section SiteLimit

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
variable {ι : Type u} [Preorder ι] (K : ι → Ideal A) (hK : Monotone K)

/-- The transition morphism `Spec (A/K i) ⟶ Spec (A/K j)` for `K j ≤ K i`. -/
noncomputable def quotientBaseTransition {i j : ι} (hji : j ≤ i) :
    quotientBase A B hA (K i) ⟶ quotientBase A B hA (K j) := by
  refine Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hK hji))) :
      Spec (.of (A ⧸ K i)) ⟶ Spec (.of (A ⧸ K j)))) ?_
  apply B.inclusion.map_injective
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hK hji))) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (K j))) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (K i)))
  rw [← Spec.map_comp]
  congr 1

/-- The inverse system of the quotient bases `Spec (A/K i)` of a monotone family of
ideals. -/
noncomputable def quotientBaseDiagram : ιᵒᵖ ⥤ BigFppfOver B (Spec (.of A)) hA where
  obj i := quotientBase A B hA (K i.unop)
  map f := quotientBaseTransition A B hA K hK (leOfHom f.unop)
  map_id i := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    dsimp [quotientBaseTransition]
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hK le_rfl))) = 𝟙 _
    simp
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    dsimp [quotientBaseTransition]
    change Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (hK (leOfHom (f ≫ g).unop)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hK (leOfHom f.unop)))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hK (leOfHom g.unop))))
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    change Ideal.Quotient.factor (S := K _) (T := K _) (hK (leOfHom (f ≫ g).unop)) =
      (Ideal.Quotient.factor (S := K _) (T := K _) (hK (leOfHom f.unop))).comp
        (Ideal.Quotient.factor (S := K _) (T := K _) (hK (leOfHom g.unop)))
    rw [Ideal.Quotient.factor_comp]

/-- The diagram of quotient bases, with the structure morphisms to `Spec A` forgotten. -/
noncomputable abbrev quotientBaseUnderlyingDiagram :
    ιᵒᵖ ⥤ B.Schemes :=
  quotientBaseDiagram A B hA K hK ⋙ Over.forget (B.obj hA)

/-- The cone on the underlying diagram of quotient bases with vertex `Spec (A/⨆ K)`. -/
noncomputable def quotientBaseUnderlyingCone :
    Cone (quotientBaseUnderlyingDiagram A B hA K hK) := by
  refine Cone.mk (B.obj (B.contains_spec_quotient hA (⨆ i, K i)))
    { app := fun i => ObjectProperty.homMk
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_iSup K i.unop))))
      naturality := ?_ }
  intro i j f
  apply B.inclusion.map_injective
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_iSup K j.unop))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_iSup K i.unop))) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hK (leOfHom f.unop))))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  change Ideal.Quotient.factor (S := K j.unop) (T := ⨆ k, K k) (le_iSup K j.unop) =
    (Ideal.Quotient.factor (S := K i.unop) (T := ⨆ k, K k) (le_iSup K i.unop)).comp
      (Ideal.Quotient.factor (S := K j.unop) (T := K i.unop) (hK (leOfHom f.unop)))
  rw [Ideal.Quotient.factor_comp]

/-- `Spec (A/⨆ K)` is the limit of the `Spec (A/K i)` inside the big fppf site: it is their
limit in schemes because `Spec` turns the colimit
`AlgebraicGeometry.Space.isColimitQuotientRingCocone` into a limit, and the inclusion of the
site into schemes is fully faithful, so it reflects a limit whose vertex is already an
object of the site. -/
noncomputable def isLimitQuotientBaseUnderlyingCone [Nonempty ι] [IsDirected ι (· ≤ ·)] :
    IsLimit (quotientBaseUnderlyingCone A B hA K hK) := by
  let cS := Scheme.Spec.mapCone (quotientRingCocone K hK).op
  have hcS : IsLimit cS :=
    isLimitOfPreserves Scheme.Spec (isColimitQuotientRingCocone K hK).op
  have hD : quotientBaseUnderlyingDiagram A B hA K hK ⋙ B.inclusion =
      (quotientRingDiagram K hK).op ⋙ Scheme.Spec := rfl
  have hcone : cS ≅ B.inclusion.mapCone (quotientBaseUnderlyingCone A B hA K hK) := by
    cases hD
    exact Cone.ext (Iso.refl _)
  exact isLimitOfReflects B.inclusion (hcS.ofIsoLimit hcone)

/-- The natural transformation recording the structure morphisms of the quotient bases. -/
noncomputable def quotientBaseToBase :
    quotientBaseUnderlyingDiagram A B hA K hK ⟶ (Functor.const ιᵒᵖ).obj (B.obj hA) where
  app i := ((quotientBaseDiagram A B hA K hK).obj i).hom
  naturality _ _ f := ((quotientBaseDiagram A B hA K hK).map f).w

/-- The compatibility of the cone with vertex `Spec (A/⨆ K)` with the structure morphisms to
`Spec A`. -/
theorem quotientBaseUnderlyingCone_comp_toBase (i : ιᵒᵖ) :
    (quotientBaseUnderlyingCone A B hA K hK).π.app i ≫
        (quotientBaseToBase A B hA K hK).app i =
      (quotientBase A B hA (⨆ i, K i)).hom := by
  apply B.inclusion.map_injective
  show Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_iSup K i.unop))) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (K i.unop))) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⨆ i, K i)))
  rw [← Spec.map_comp]
  congr 1

/-- The cone on the diagram of quotient bases, in the site over `Spec A`, with vertex
`Spec (A/⨆ K)`. -/
noncomputable def quotientBaseCone : Cone (quotientBaseDiagram A B hA K hK) :=
  Over.liftCone (quotientBaseUnderlyingDiagram A B hA K hK) (quotientBaseToBase A B hA K hK)
    (quotientBaseUnderlyingCone A B hA K hK) (quotientBase A B hA (⨆ i, K i)).hom
    (quotientBaseUnderlyingCone_comp_toBase A B hA K hK)

/-- `Spec (A/⨆ K)`, with its structure morphism to `Spec A`, is the limit of the quotient
bases in the site over `Spec A`: the slice projection creates limits of connected diagrams,
and a directed index category is connected. -/
noncomputable def isLimitQuotientBaseCone [Nonempty ι] [IsDirected ι (· ≤ ·)] :
    IsLimit (quotientBaseCone A B hA K hK) := by
  have _ : Nonempty ιᵒᵖ := ⟨op (Classical.choice ‹Nonempty ι›)⟩
  exact Over.isLimitLiftCone (quotientBaseUnderlyingDiagram A B hA K hK)
    (quotientBaseToBase A B hA K hK) (quotientBaseUnderlyingCone A B hA K hK)
    (quotientBase A B hA (⨆ i, K i)).hom
    (quotientBaseUnderlyingCone_comp_toBase A B hA K hK)
    (isLimitQuotientBaseUnderlyingCone A B hA K hK)

end SiteLimit

/-! ### The base changes as a limit situation -/

section BaseChangeLimit

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
variable {ι : Type u} [Preorder ι] (K : ι → Ideal A) (hK : Monotone K)

/-- The terminal object `Spec A` of the site, read as a presheaf, is terminal there. -/
noncomputable def isTerminalYonedaAffineBase :
    IsTerminal (yoneda.obj (affineBaseObject A B hA)) :=
  IsTerminal.isTerminalObj yoneda (affineBaseObject A B hA) Over.mkIdTerminal

/-- The inverse system of quotient bases, read as presheaves. -/
noncomputable abbrev quotientBasePresheafDiagram :
    ιᵒᵖ ⥤ ((BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u) :=
  quotientBaseDiagram A B hA K hK ⋙ yoneda

/-- The structure morphisms of the quotient bases to `Spec A`, read as presheaves. Their
naturality is terminality of `Spec A` in the site. -/
noncomputable def quotientBasePresheafToBase :
    quotientBasePresheafDiagram A B hA K hK ⟶
      (Functor.const ιᵒᵖ).obj (yoneda.obj (affineBaseObject A B hA)) where
  app i := yoneda.map (quotientBaseHom A B hA (K i.unop))
  naturality _ _ _ := (isTerminalYonedaAffineBase A B hA).hom_ext _ _

variable {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
variable (φ : X ⟶ yoneda.obj (affineBaseObject A B hA))

/-- The inverse system of base changes `X_{A/K i}`. -/
noncomputable abbrev quotientSpaceDiagram :
    ιᵒᵖ ⥤ ((BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u) :=
  Over.lift (quotientBasePresheafDiagram A B hA K hK)
      (quotientBasePresheafToBase A B hA K hK) ⋙
    Over.pullback φ ⋙ Over.forget X

/-- The stages of `AlgebraicGeometry.Space.quotientSpaceDiagram` are the base changes. -/
theorem quotientSpaceDiagram_obj (i : ιᵒᵖ) :
    (quotientSpaceDiagram A B hA K hK φ).obj i = quotientSpace A B hA φ (K i.unop) :=
  rfl

/-- The transition morphisms of `AlgebraicGeometry.Space.quotientSpaceDiagram` are the
induced maps of fibre products. -/
theorem quotientSpaceDiagram_map {i j : ιᵒᵖ} (f : i ⟶ j) :
    (quotientSpaceDiagram A B hA K hK φ).map f =
      pullback.map
        ((quotientBasePresheafToBase A B hA K hK).app i) φ
        ((quotientBasePresheafToBase A B hA K hK).app j) φ
        (yoneda.map ((quotientBaseDiagram A B hA K hK).map f)) (𝟙 X)
        (𝟙 (yoneda.obj (affineBaseObject A B hA)))
        (((quotientBasePresheafToBase A B hA K hK).naturality f).symm) (by simp) :=
  rfl

/-- Each transition square of the system of base changes is Cartesian: base changing the
Cartesian square defining `X_{A/K j}` along the transition `Spec (A/K i) ⟶ Spec (A/K j)`
gives the square defining `X_{A/K i}`. -/
theorem isPullback_quotientSpaceDiagram_map {i j : ιᵒᵖ} (f : i ⟶ j) :
    IsPullback
      (pullback.fst ((quotientBasePresheafToBase A B hA K hK).app i) φ)
      ((quotientSpaceDiagram A B hA K hK φ).map f)
      (yoneda.map ((quotientBaseDiagram A B hA K hK).map f))
      (pullback.fst ((quotientBasePresheafToBase A B hA K hK).app j) φ) := by
  set t := quotientBasePresheafToBase A B hA K hK with ht
  set a := yoneda.map ((quotientBaseDiagram A B hA K hK).map f) with ha
  have hcomp : a ≫ t.app j = t.app i := t.naturality f
  set m : pullback (t.app i) φ ⟶ pullback (t.app j) φ :=
    pullback.map (t.app i) φ (t.app j) φ a (𝟙 X)
      (𝟙 (yoneda.obj (affineBaseObject A B hA)))
      ((Category.comp_id _).trans hcomp.symm) (by simp) with hm
  have hfirst : m ≫ pullback.fst (t.app j) φ = pullback.fst (t.app i) φ ≫ a :=
    pullback.lift_fst _ _ _
  have hsecond' : m ≫ pullback.snd (t.app j) φ = pullback.snd (t.app i) φ ≫ 𝟙 X :=
    pullback.lift_snd _ _ _
  have hsecond : m ≫ pullback.snd (t.app j) φ = pullback.snd (t.app i) φ := by
    rw [hsecond', Category.comp_id]
  have hPasted : IsPullback (pullback.fst (t.app i) φ)
      (m ≫ pullback.snd (t.app j) φ) (a ≫ t.app j) φ := by
    rw [hsecond, hcomp]
    exact IsPullback.of_hasPullback (t.app i) φ
  exact hPasted.of_bot hfirst.symm (IsPullback.of_hasPullback (t.app j) φ)

/-- Each transition morphism of the diagram of quotient bases is a closed immersion of
schemes: it is `Spec` of the surjection `A/K j ↠ A/K i` given by `Ideal.Quotient.factor`. -/
theorem isClosedImmersion_toScheme_map_quotientBaseDiagram_map {i j : ιᵒᵖ} (f : i ⟶ j) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
        ((quotientBaseDiagram A B hA K hK).map f)) := by
  show _root_.AlgebraicGeometry.IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hK (leOfHom f.unop)))))
  exact _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    (Ideal.Quotient.factor_surjective (hK (leOfHom f.unop)))

/-- **The transition morphisms of the system of base changes are closed immersions**, not
merely affine: they are base changes of `Spec (A/K i) ⟶ Spec (A/K j)`, which is `Spec` of a
surjection. This is what puts the system in the scope of Stacks 07SR for closed-immersion
transitions, which needs no bound on the index. -/
theorem isClosedImmersion_quotientSpaceDiagram_map {i j : ιᵒᵖ} (f : i ⟶ j) :
    IsClosedImmersion B (Spec (.of A)) hA ((quotientSpaceDiagram A B hA K hK φ).map f) :=
  (isClosedImmersion_isStableUnderBaseChange B (Spec (.of A)) hA).of_isPullback
    (isPullback_quotientSpaceDiagram_map A B hA K hK φ f)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B (Spec (.of A)) hA
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
        ((quotientBaseDiagram A B hA K hK).map f)).2
      (isClosedImmersion_toScheme_map_quotientBaseDiagram_map A B hA K hK f))

/-- The transition morphisms of the system of base changes are affine, being base changes of
the transition morphisms `Spec (A/K i) ⟶ Spec (A/K j)`, which are morphisms of affine
schemes. -/
theorem isAffineHom_quotientSpaceDiagram_map {i j : ιᵒᵖ} (f : i ⟶ j) :
    IsAffineHom B (Spec (.of A)) hA ((quotientSpaceDiagram A B hA K hK φ).map f) :=
  IsAffineHom.of_isPullback (isPullback_quotientSpaceDiagram_map A B hA K hK φ f)
    (@isAffineHom_yoneda_map B (Spec (.of A)) hA _ _ ((quotientBaseDiagram A B hA K hK).map f)
      (isAffine_quotientBase A B hA (K i.unop)) (isAffine_quotientBase A B hA (K j.unop)))

/-- The limiting cone on the system of base changes, with vertex `X_{A/⨆ K}`: the quotient
bases have `Spec (A/⨆ K)` as limit in the site, and base change along `φ` preserves that
limit because the index category is connected. -/
noncomputable def quotientSpaceLimitCone [Nonempty ι] [IsDirected ι (· ≤ ·)] :
    Cone (quotientSpaceDiagram A B hA K hK φ) :=
  (Over.forget X).mapCone ((Over.pullback φ).mapCone
    (Over.liftCone (quotientBasePresheafDiagram A B hA K hK)
      (quotientBasePresheafToBase A B hA K hK)
      (yoneda.mapCone (quotientBaseCone A B hA K hK))
      (yoneda.map (quotientBaseHom A B hA (⨆ i, K i)))
      (fun _ => (isTerminalYonedaAffineBase A B hA).hom_ext _ _)))

/-- The vertex of `AlgebraicGeometry.Space.quotientSpaceLimitCone` is the base change to the
quotient by the supremum of the family. -/
theorem quotientSpaceLimitCone_pt [Nonempty ι] [IsDirected ι (· ≤ ·)] :
    (quotientSpaceLimitCone A B hA K hK φ).pt = quotientSpace A B hA φ (⨆ i, K i) :=
  rfl

/-- `AlgebraicGeometry.Space.quotientSpaceLimitCone` is limiting. -/
noncomputable def isLimitQuotientSpaceLimitCone [Nonempty ι] [IsDirected ι (· ≤ ·)] :
    IsLimit (quotientSpaceLimitCone A B hA K hK φ) := by
  have _ : Nonempty ιᵒᵖ := ⟨op (Classical.choice ‹Nonempty ι›)⟩
  have _ : IsConnected ιᵒᵖ := IsCofiltered.isConnected _
  exact isLimitOfPreserves (Over.forget X)
    (isLimitOfPreserves (Over.pullback φ)
      (Over.isLimitLiftCone (quotientBasePresheafDiagram A B hA K hK)
        (quotientBasePresheafToBase A B hA K hK)
        (yoneda.mapCone (quotientBaseCone A B hA K hK))
        (yoneda.map (quotientBaseHom A B hA (⨆ i, K i)))
        (fun _ => (isTerminalYonedaAffineBase A B hA).hom_ext _ _)
        (isLimitOfPreserves yoneda (isLimitQuotientBaseCone A B hA K hK))))

end BaseChangeLimit

/-! ### Situation 084R for the quotient base changes -/

section DescentSituation

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))

variable {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
variable (φ : X ⟶ yoneda.obj (affineBaseObject A B hA))

/-- The base `Spec A`, read as a presheaf, is an algebraic space. -/
theorem isAlgebraicSpace_yoneda_affineBaseObject :
    IsAlgebraicSpace B (Spec (.of A)) hA (yoneda.obj (affineBaseObject A B hA)) :=
  isAlgebraicSpace_yoneda B (Spec (.of A)) hA (affineBaseObject A B hA)

/-- A quasi-compact structure morphism to the affine base makes the space quasi-compact: the
base change of `φ` along the identity of `Spec A`, which is quasi-compact because `Spec A` is,
is isomorphic to the space. -/
theorem isQuasiCompactSpace_of_isQuasiCompact_toAffineBase
    (hqc : IsQuasiCompact B (Spec (.of A)) hA φ) :
    IsQuasiCompactSpace B (Spec (.of A)) hA X := by
  have hpbqc := hqc _ (isAlgebraicSpace_yoneda_affineBaseObject A B hA)
    (isQuasiCompactSpace_yoneda_of_isAffine B (Spec (.of A)) hA (affineBaseObject A B hA)
      inferInstance) (𝟙 _)
  have hpb : IsPullback (pullback.fst (𝟙 (yoneda.obj (affineBaseObject A B hA))) φ)
      (pullback.snd (𝟙 (yoneda.obj (affineBaseObject A B hA))) φ)
      (𝟙 (yoneda.obj (affineBaseObject A B hA))) φ :=
    IsPullback.of_hasPullback _ _
  have _ : IsIso (pullback.snd (𝟙 (yoneda.obj (affineBaseObject A B hA))) φ) :=
    hpb.isIso_snd_of_isIso
  exact IsQuasiCompactSpace.of_iso B (Spec (.of A)) hA hpbqc
    (asIso (pullback.snd (𝟙 (yoneda.obj (affineBaseObject A B hA))) φ))

/-- A quasi-separated structure morphism to the affine base makes the space quasi-separated:
`Spec A` is quasi-separated, and Stacks 04ZH part (2) passes that to the source. -/
theorem isAbsolutelyQuasiSeparated_of_isQuasiSeparated_toAffineBase
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hqs : IsQuasiSeparated B (Spec (.of A)) hA φ) :
    IsAbsolutelyQuasiSeparated B (Spec (.of A)) hA B.contains_terminal X :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (Spec (.of A)) hA B.contains_terminal hX
    (isAbsolutelyQuasiSeparated_yoneda_of_isAffine B (Spec (.of A)) hA B.contains_terminal
      (affineBaseObject A B hA) inferInstance) hqs

variable {ι : Type u} [Preorder ι] (K : ι → Ideal A) (hK : Monotone K)

/-- The base `Spec (A/I)`, read as a presheaf, is an algebraic space. -/
private theorem isAlgebraicSpace_yoneda_quotientBase (I : Ideal A) :
    IsAlgebraicSpace B (Spec (.of A)) hA (yoneda.obj (quotientBase A B hA I)) :=
  isAlgebraicSpace_yoneda B (Spec (.of A)) hA _

/-- The base change `X_{A/I}` of an algebraic space over `Spec A` is an algebraic space. -/
theorem isAlgebraicSpace_quotientSpace (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (I : Ideal A) : IsAlgebraicSpace B (Spec (.of A)) hA (quotientSpace A B hA φ I) :=
  isAlgebraicSpace_pullback B (Spec (.of A)) hA _ φ
    (isAlgebraicSpace_yoneda_quotientBase A B hA I) hX
    (isAlgebraicSpace_yoneda_affineBaseObject A B hA)

/-- The base change `X_{A/I}` of a quasi-compact algebraic space over `Spec A` is
quasi-compact: it is a fibre product of quasi-compact algebraic spaces over the
quasi-separated `Spec A`. -/
theorem isQuasiCompactSpace_quotientSpace
    (hXqc : IsQuasiCompactSpace B (Spec (.of A)) hA X) (I : Ideal A) :
    IsQuasiCompactSpace B (Spec (.of A)) hA (quotientSpace A B hA φ I) :=
  isQuasiCompactSpace_pullback B (Spec (.of A)) hA B.contains_terminal _ φ
    (isAlgebraicSpace_yoneda_quotientBase A B hA I)
    (isAlgebraicSpace_yoneda_affineBaseObject A B hA)
    (isQuasiCompactSpace_yoneda_of_isAffine B (Spec (.of A)) hA (quotientBase A B hA I)
      inferInstance)
    hXqc
    (isAbsolutelyQuasiSeparated_yoneda_of_isAffine B (Spec (.of A)) hA B.contains_terminal
      (affineBaseObject A B hA) inferInstance)

/-- The base change `X_{A/I}` of a quasi-separated algebraic space over `Spec A` is
quasi-separated: it is a fibre product of quasi-separated algebraic spaces. -/
theorem isAbsolutelyQuasiSeparated_quotientSpace (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hXqs : IsAbsolutelyQuasiSeparated B (Spec (.of A)) hA B.contains_terminal X)
    (I : Ideal A) :
    IsAbsolutelyQuasiSeparated B (Spec (.of A)) hA B.contains_terminal
      (quotientSpace A B hA φ I) :=
  isAbsolutelyQuasiSeparated_pullback B (Spec (.of A)) hA B.contains_terminal _ φ
    (isAlgebraicSpace_yoneda_quotientBase A B hA I) hX
    (isAlgebraicSpace_yoneda_affineBaseObject A B hA)
    (isAbsolutelyQuasiSeparated_yoneda_of_isAffine B (Spec (.of A)) hA B.contains_terminal
      (quotientBase A B hA I) inferInstance)
    hXqs

/-- **Situation 084R for the quotient base changes.** For a directed monotone family of
ideals `K` of `A` and a quasi-compact, quasi-separated algebraic space `X` over `Spec A`, the
base changes `X_{A/K i}` form a limit situation whose limit is `X_{A/⨆ K}`. -/
noncomputable def quotientDescentSituation [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hXqc : IsQuasiCompactSpace B (Spec (.of A)) hA X)
    (hXqs : IsAbsolutelyQuasiSeparated B (Spec (.of A)) hA B.contains_terminal X)
    (base : ι) :
    DescentSituation B (Spec (.of A)) hA B.contains_terminal ι where
  system := quotientSpaceDiagram A B hA K hK φ
  algebraicSpace i := isAlgebraicSpace_quotientSpace A B hA φ hX (K i)
  transition_affine f := isAffineHom_quotientSpaceDiagram_map A B hA K hK φ f
  quasiCompact i := isQuasiCompactSpace_quotientSpace A B hA φ hXqc (K i)
  quasiSeparated i := isAbsolutelyQuasiSeparated_quotientSpace A B hA φ hX hXqs (K i)
  limitCone := quotientSpaceLimitCone A B hA K hK φ
  isLimit := isLimitQuotientSpaceLimitCone A B hA K hK φ
  limitAlgebraicSpace := isAlgebraicSpace_quotientSpace A B hA φ hX (⨆ i, K i)
  base := base

end DescentSituation

/-! ### The base change along `A → A/0` -/

section Bot

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))

/-- `Spec (A/0) ⟶ Spec A` is an isomorphism of objects of the site over `Spec A`. -/
theorem isIso_quotientBaseHom_bot : IsIso (quotientBaseHom A B hA (⊥ : Ideal A)) := by
  have hmk : Ideal.Quotient.mk (⊥ : Ideal A) = (RingEquiv.quotientBot A).symm.toRingHom := by
    ext a
    simp
  have hSpec : IsIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal A)))) := by
    rw [hmk]
    exact (Scheme.Spec.mapIso (RingEquiv.quotientBot A).symm.toCommRingCatIso.op).isIso_hom
  have hB : IsIso (B.inclusion.map (quotientBase A B hA (⊥ : Ideal A)).hom) := hSpec
  have hObj : IsIso (quotientBase A B hA (⊥ : Ideal A)).hom :=
    (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map _
  have hForget : IsIso ((Over.forget (B.obj hA)).map (quotientBaseHom A B hA (⊥ : Ideal A))) :=
    hObj
  exact isIso_of_reflects_iso (quotientBaseHom A B hA (⊥ : Ideal A)) (Over.forget (B.obj hA))

variable {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
variable (φ : X ⟶ yoneda.obj (affineBaseObject A B hA))

/-- The base change of `X` along `A → A/0` is isomorphic to `X`. -/
noncomputable def quotientSpaceBotIso : quotientSpace A B hA φ (⊥ : Ideal A) ≅ X :=
  let : IsIso (quotientBaseHom A B hA (⊥ : Ideal A)) := isIso_quotientBaseHom_bot A B hA
  let : IsIso (yoneda.map (quotientBaseHom A B hA (⊥ : Ideal A))) := inferInstance
  have hiso : IsIso (pullback.snd (yoneda.map (quotientBaseHom A B hA (⊥ : Ideal A))) φ) :=
    (IsPullback.of_hasPullback
      (yoneda.map (quotientBaseHom A B hA (⊥ : Ideal A))) φ).isIso_snd_of_isIso
  @asIso _ _ _ _ _ hiso

end Bot

/-! ### Stacks 0B81 -/

section Main

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
variable {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
variable (φ : X ⟶ yoneda.obj (affineBaseObject A B hA))

/-- **The Zorn skeleton of Stacks 0B81.** Given that the supremum of a nonempty chain of
ideals whose base changes are all non-schematic is again non-schematic, there is a maximal
such ideal. The set is nonempty because `X_{A/0} ≅ X` is not a scheme.

The chain step is isolated as a hypothesis so that the Zorn bookkeeping is separated from the
appeal to Stacks 07SR which supplies it; see
`AlgebraicGeometry.Space.exists_maximal_not_isRepresentable_quotientSpace`. -/
theorem exists_maximal_not_isRepresentable_quotientSpace_of_chainStep
    (hnot : ¬ X.IsRepresentable)
    (hstep : ∀ c : Set (Ideal A),
      (∀ J ∈ c, ¬ (quotientSpace A B hA φ J).IsRepresentable) → c.Nonempty →
      IsChain (· ≤ ·) c → ¬ (quotientSpace A B hA φ (sSup c)).IsRepresentable) :
    ∃ I : Ideal A, ¬ (quotientSpace A B hA φ I).IsRepresentable ∧
      ∀ I' : Ideal A, I < I' → (quotientSpace A B hA φ I').IsRepresentable := by
  classical
  set bad : Set (Ideal A) := {I | ¬ (quotientSpace A B hA φ I).IsRepresentable} with hbad
  have hbot : (⊥ : Ideal A) ∈ bad := by
    intro hrep
    let : (quotientSpace A B hA φ (⊥ : Ideal A)).IsRepresentable := hrep
    exact hnot (isRepresentable_of_natIso (quotientSpace A B hA φ (⊥ : Ideal A))
      (quotientSpaceBotIso A B hA φ))
  have hchains : ∀ c ⊆ bad, IsChain (· ≤ ·) c → ∃ ub ∈ bad, ∀ J ∈ c, J ≤ ub := by
    intro c hc hchain
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨⊥, hbot, by simp⟩
    · exact ⟨sSup c, hstep c (fun _ hJ => hc hJ) hne hchain, fun _ hJ => le_sSup hJ⟩
  obtain ⟨M, hM, hMmax⟩ := zorn_le₀ bad hchains
  refine ⟨M, hM, ?_⟩
  intro J hMJ
  by_contra hJ
  exact absurd (hMmax hJ hMJ.le) (not_le_of_gt hMJ)

/-- **The chain step of Stacks 0B81, from any directed subfamily of the chain with the same
supremum.** Zorn's lemma asks for an upper bound of each chain, never for one computed from
the chain as presented, so the limit argument may be run over a subfamily — which is what
makes the *index* of the limit situation negotiable even when the chain itself is not, and
which is what lets one Zorn proof serve both a size-free and a size-bounded Stacks 07SR. -/
theorem not_isRepresentable_quotientSpace_sSup_of_subfamily
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hXqc : IsQuasiCompactSpace B (Spec (.of A)) hA X)
    (hXqs : IsAbsolutelyQuasiSeparated B (Spec (.of A)) hA B.contains_terminal X)
    {c : Set (Ideal A)} (hc : ∀ J ∈ c, ¬ (quotientSpace A B hA φ J).IsRepresentable)
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (K : ι → Ideal A) (hK : Monotone K) (base : ι)
    (hmem : ∀ i, K i ∈ c) (hsup : ⨆ i, K i = sSup c)
    (hstage :
      (quotientDescentSituation A B hA φ K hK hX hXqc hXqs base).limitCone.pt.IsRepresentable →
        ∃ i : ι, ((quotientDescentSituation A B hA φ K hK hX hXqc hXqs base).system.obj
          (op i)).IsRepresentable) :
    ¬ (quotientSpace A B hA φ (sSup c)).IsRepresentable := by
  intro hrep
  rw [← hsup] at hrep
  obtain ⟨i, hi⟩ := hstage hrep
  exact hc _ (hmem i) hi

/-- **Stacks 0B81.** Let `φ : X ⟶ Spec A` be a quasi-compact and quasi-separated morphism from
an algebraic space to an affine scheme. If `X` is not a scheme then there is an ideal `I ⊂ A`
such that the base change `X_{A/I}` is not a scheme while `X_{A/I'}` is a scheme for every
ideal `I'` with `I ⊊ I'`.

By Zorn's lemma applied to the set of ideals `I` with `X_{A/I}` not a scheme. It contains
`(0)` because `X_{A/0} ≅ X`, and the supremum of a chain of such ideals is again one of them
because `X_{A/⨆ K}` is the limit of the `X_{A/K i}`
(`AlgebraicGeometry.Space.quotientDescentSituation`), so Stacks 07SR makes one member of the
chain a scheme. A maximal element is the required ideal.

Nothing is assumed beyond the tag's own hypotheses, and in particular no bound on the chain and
no condition on the site's size cutoff. Stacks 07SR is
`AlgebraicGeometry.Space.DescentSituation.exists_isRepresentable_system_obj_of_isSiteSmall`, whose
smallness hypothesis is met by `AlgebraicGeometry.Space.IsSiteSmall.of_mono`: the transition
morphisms of this system are closed immersions, by
`AlgebraicGeometry.Space.isClosedImmersion_quotientSpaceDiagram_map`, because `A/K i ↠ A/K j`
is surjective, hence monomorphisms, and for such a system nothing is asked of the index. -/
@[stacks 0B81]
theorem exists_maximal_not_isRepresentable_quotientSpace
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hqc : IsQuasiCompact B (Spec (.of A)) hA φ)
    (hqs : IsQuasiSeparated B (Spec (.of A)) hA φ)
    (hnot : ¬ X.IsRepresentable) :
    ∃ I : Ideal A, ¬ (quotientSpace A B hA φ I).IsRepresentable ∧
      ∀ I' : Ideal A, I < I' → (quotientSpace A B hA φ I').IsRepresentable := by
  classical
  have hXqc : IsQuasiCompactSpace B (Spec (.of A)) hA X :=
    isQuasiCompactSpace_of_isQuasiCompact_toAffineBase A B hA φ hqc
  have hXqs : IsAbsolutelyQuasiSeparated B (Spec (.of A)) hA B.contains_terminal X :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated_toAffineBase A B hA φ hX hqs
  refine exists_maximal_not_isRepresentable_quotientSpace_of_chainStep A B hA φ hnot ?_
  rintro c hc ⟨J₀, hJ₀⟩ hchain
  have _ : Nonempty ↥c := ⟨⟨J₀, hJ₀⟩⟩
  have _ : IsDirected ↥c (· ≤ ·) := by
    refine ⟨fun i j => ?_⟩
    rcases eq_or_ne i.1 j.1 with h | h
    · exact ⟨j, h.le, le_rfl⟩
    · rcases hchain i.2 j.2 h with h' | h'
      · exact ⟨j, h', le_rfl⟩
      · exact ⟨i, le_rfl, h'⟩
  exact not_isRepresentable_quotientSpace_sSup_of_subfamily A B hA φ hX hXqc hXqs hc
    (fun i : ↥c => i.1) (fun _ _ h => h) ⟨J₀, hJ₀⟩ (fun i => i.2) (sSup_eq_iSup' c).symm
    (DescentSituation.exists_isRepresentable_system_obj_of_isSiteSmall
      (quotientDescentSituation A B hA φ (fun i : ↥c => i.1) (fun _ _ h => h)
        hX hXqc hXqs ⟨J₀, hJ₀⟩)
      (.of_mono fun {_ _} f => mono_of_isClosedImmersion B (Spec (.of A)) hA _
        (isClosedImmersion_quotientSpaceDiagram_map A B hA
          (fun i : ↥c => i.1) (fun _ _ h => h) φ f)))

/-- The base change `X_{A/I}`, which is a fibre product over the terminal object `Spec A`, is
the product of `X` with `Spec (A/I)`. -/
noncomputable def quotientSpaceIsoProd (I : Ideal A) :
    quotientSpace A B hA φ I ≅
      FunctorToTypes.prod (yoneda.obj (quotientBase A B hA I)) X := by
  have hT := isTerminalYonedaAffineBase A B hA
  have hPB : IsPullback
      (prod.fst : yoneda.obj (quotientBase A B hA I) ⨯ X ⟶ _) prod.snd
      (yoneda.map (quotientBaseHom A B hA I)) φ := by
    rw [hT.hom_ext (yoneda.map (quotientBaseHom A B hA I)) (hT.from _), hT.hom_ext φ (hT.from X)]
    exact IsPullback.of_is_product' (prodIsProd (yoneda.obj (quotientBase A B hA I)) X) hT
  exact hPB.isoPullback.symm ≪≫
    FunctorToTypes.binaryProductIso (yoneda.obj (quotientBase A B hA I)) X

/-- **The two readings of "the base change `X_{A/I}` is a scheme" agree.** The fibre product
`X ×_{Spec A} Spec (A/I)`, read as a presheaf over `Spec A`, is representable exactly when the
restriction of `X` to the big fppf site over `Spec (A/I)` — the base change as a space over its
own base, Stacks 03I5 part (1) — is.

Over the terminal object `Spec A` the fibre product is a product, so this is
`CategoryTheory.OverShriek.isRepresentable_relocalizeRestrict_iff`. -/
theorem isRepresentable_quotientSpace_iff (I : Ideal A) :
    (quotientSpace A B hA φ I).IsRepresentable ↔
      ((OverShriek.relocalizeRestrict (quotientBase A B hA I).hom).obj X).IsRepresentable := by
  rw [OverShriek.isRepresentable_relocalizeRestrict_iff]
  constructor
  · intro h
    let : (quotientSpace A B hA φ I).IsRepresentable := h
    exact isRepresentable_of_natIso _ (quotientSpaceIsoProd A B hA φ I)
  · intro h
    let : (FunctorToTypes.prod (yoneda.obj (quotientBase A B hA I)) X).IsRepresentable := h
    exact isRepresentable_of_natIso _ (quotientSpaceIsoProd A B hA φ I).symm

/-- **Stacks 0B81 in the restriction reading of base change.** The same
statement as `AlgebraicGeometry.Space.exists_maximal_not_isRepresentable_quotientSpace`, with
`X_{A/I}` read as the restriction of `X` to the big fppf site over `Spec (A/I)` rather than as
the fibre product over `Spec A`. The two readings agree by
`AlgebraicGeometry.Space.isRepresentable_quotientSpace_iff`. -/
theorem exists_maximal_not_isRepresentable_relocalizeRestrict
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hqc : IsQuasiCompact B (Spec (.of A)) hA φ)
    (hqs : IsQuasiSeparated B (Spec (.of A)) hA φ)
    (hnot : ¬ X.IsRepresentable) :
    ∃ I : Ideal A,
      ¬ ((OverShriek.relocalizeRestrict (quotientBase A B hA I).hom).obj X).IsRepresentable ∧
        ∀ I' : Ideal A, I < I' →
          ((OverShriek.relocalizeRestrict (quotientBase A B hA I').hom).obj X).IsRepresentable := by
  obtain ⟨I, hI, hI'⟩ :=
    exists_maximal_not_isRepresentable_quotientSpace A B hA φ hX hqc hqs hnot
  exact ⟨I, fun hcon => hI ((isRepresentable_quotientSpace_iff A B hA φ I).mpr hcon),
    fun I' hlt => (isRepresentable_quotientSpace_iff A B hA φ I').mp (hI' I' hlt)⟩

end Main

end Space

end AlgebraicGeometry

end
