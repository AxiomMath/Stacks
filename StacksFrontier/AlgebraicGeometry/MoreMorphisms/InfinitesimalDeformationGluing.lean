module

public import StacksFrontier.AlgebraicGeometry.Conormal.ModuleCoverLocality
public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictSquareIso
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationSheaf

/-!
# The sheaf of constrained lifts of a morphism along a first order thickening

Let `S` be a scheme, let `i : X ⟶ X'` and `j : Y ⟶ Y'` be immersions, let `a : X ⟶ Y` be a
morphism and let `A : a^* 𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` be a map of `𝒪_X`-modules. For an open `V` of `X'`,
`Stacks.Thickenings.compatibleLifts` is the set of [Stacks Project, Tag 04FI]: the morphisms
`b : V ⟶ Y'` over `S` restricting to `a` on `i⁻¹V` and inducing the restriction of `A` there.
This file proves [Stacks Project, Tag 04FH]: `V ↦ {b}` is a **sheaf of sets** on `X'`.

## Main definitions

* `Stacks.Thickenings.openCoverOfOpens`: the open cover of an open subscheme by a family of
  smaller opens covering it.
* `Stacks.Thickenings.glueCompatibleLifts`: the morphism `⨆ V_k ⟶ Y'` glued from a family of
  lifts agreeing on the pairwise intersections.

## Main results

* `Stacks.Thickenings.isCompatibleLift_glueCompatibleLifts`: the glued morphism is again a
  compatible lift. All three conditions of [Stacks Project, Tag 04FI] are local on `X'`: the
  first two because a morphism of schemes is determined by its restrictions to an open cover, the
  third because a morphism of sheaves of modules is
  (`RingedSpaceModuleAdjunction.modulePullback_homOfLE_map_injective`).
* `Stacks.Thickenings.isSheaf_compatibleLiftsPresheaf`: **[Stacks Project, Tag 04FH]**, the sheaf
  property of `Stacks.Thickenings.compatibleLiftsPresheaf`.
* `Stacks.Thickenings.isSheaf_firstOrderCompatibleLiftsPresheaf`: the same statement in the
  first-order-thickening setting in which the tag is stated.

## Implementation notes

The source's proof is "the sheaf property is immediate, since morphisms are defined locally". The
locality of a *morphism of schemes* is `AlgebraicGeometry.Scheme.Cover.glueMorphisms` and
`AlgebraicGeometry.Scheme.Cover.hom_ext`, and it gives conditions (1) and (2) of
[Stacks Project, Tag 04FI] directly.

Condition (3) is not a statement about morphisms of schemes but an equation between maps of
conormal sheaves on `i⁻¹V`, and its locality needs two separate inputs. The first is that both
sides restrict by the same rule along `ρ : i⁻¹V_k ⟶ i⁻¹(⨆ V_k)`: the induced map by
`Stacks.Immersion.immersionConormalSheafMap_morphismRestrict`, the restriction of `A` by
`Stacks.Thickenings.restrictConormalSheafMap_homOfLE`. Both rules end in the canonical map of the
restriction square between the two restrictions of `i`, and in the comparison isomorphism of the
pullback composition; the first of these is invertible by
`Stacks.Immersion.isIso_immersionConormalSheafMap_homOfLE`, which is what lets the two rules be
cancelled down to the pullbacks `ρ^*` of the two sides. The second input is that those pullbacks
jointly determine a morphism, which is
`RingedSpaceModuleAdjunction.modulePullback_homOfLE_map_injective`.

The cover of `i⁻¹(⨆ V_k)` used for condition (3) is by the opens `i⁻¹V_k`. Their supremum is
`i⁻¹(⨆ V_k)` but is not that open on the nose, which is why
`Stacks.Thickenings.openCoverOfOpens` takes the covered open as a parameter instead of using
`AlgebraicGeometry.Scheme.Opens.iSupOpenCover`.

Morphisms in `Type u` are a one-field structure rather than functions, so the elements of the
presheaf's restriction maps are reached through `TypeCat.ofHom`; the unique-gluing form of the
sheaf condition, `TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types`, is used because it
speaks about sections rather than about limits.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 04FH](https://stacks.math.columbia.edu/tag/04FH)
* [Stacks Project, Tag 04FI](https://stacks.math.columbia.edu/tag/04FI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.Immersion Stacks.ClosedImmersion

universe u

namespace Stacks.Thickenings

/-- **The open cover of an open subscheme by a covering family of smaller opens.** For opens
`A k ≤ B` of a scheme `X` whose union contains `B`, the inclusions `A k ⟶ B` form an open cover
of `B`.

Unlike `AlgebraicGeometry.Scheme.Opens.iSupOpenCover` the covered open is a parameter, so the
cover is available for an open that merely *equals* the union of the family. -/
def openCoverOfOpens {X : Scheme.{u}} (B : X.Opens) {J : Type*} (A : J → X.Opens)
    (hAB : ∀ k, A k ≤ B) (hcov : ∀ x : X, x ∈ B → ∃ k, x ∈ A k) : B.toScheme.OpenCover where
  I₀ := J
  X k := A k
  f k := X.homOfLE (hAB k)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨k, hk⟩ := hcov x.1 x.2
    refine ⟨k, ⟨x.1, hk⟩, ?_⟩
    apply Subtype.ext
    simp

/-- **Two morphisms out of an open subscheme agreeing on a covering family of smaller opens are
equal.** This is `AlgebraicGeometry.Scheme.Cover.hom_ext` for
`Stacks.Thickenings.openCoverOfOpens`, stated with the inclusions written out. -/
theorem hom_ext_of_opens {Xs : Scheme.{u}} {B : Xs.Opens} {K : Type*} (A : K → Xs.Opens)
    (hAB : ∀ k, A k ≤ B) (hcov : ∀ x : Xs, x ∈ B → ∃ k, x ∈ A k) {T : Scheme.{u}}
    (f g : B.toScheme ⟶ T)
    (h : ∀ k : K, Xs.homOfLE (hAB k) ≫ f = Xs.homOfLE (hAB k) ≫ g) : f = g :=
  (openCoverOfOpens B A hAB hcov).hom_ext f g h

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'}

variable [IsImmersion i] [IsImmersion j]

variable {pX' : X' ⟶ S} {pY' : Y' ⟶ S} {a : X ⟶ Y}
  {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
    immersionConormalSheaf i}
  {K : Type u} {U : K → X'.Opens} {c : ∀ k, (U k).toScheme ⟶ Y'}

/-- **The opens `i⁻¹V_k` cover `i⁻¹(⨆ V_k)`.** -/
theorem exists_mem_preimage_iSup (i : X ⟶ X') (U : K → X'.Opens) (x : X)
    (hx : x ∈ i ⁻¹ᵁ iSup U) : ∃ k, x ∈ i ⁻¹ᵁ U k := by
  have hx' : ∃ k, i.base x ∈ U k := Opens.mem_iSup.mp hx
  obtain ⟨k, hk⟩ := hx'
  exact ⟨k, hk⟩

/-- The cover of `⨆ V_k` by the `V_k`. -/
def iSupOpensCover (U : K → X'.Opens) : (iSup U).toScheme.OpenCover :=
  openCoverOfOpens (iSup U) U (fun k => le_iSup U k) (fun _ hx => Opens.mem_iSup.mp hx)

/-- The pairwise condition of `AlgebraicGeometry.Scheme.Cover.glueMorphisms` for a family of
morphisms agreeing on the pairwise intersections of the opens they are defined on.
`AlgebraicGeometry.isPullback_opens_inf_le` identifies the fibre product of the two inclusions
with the intersection. -/
theorem pullback_condition_of_inf (U : K → X'.Opens) (c : ∀ k, (U k).toScheme ⟶ Y')
    (hc : ∀ k l, X'.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ c k =
      X'.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ c l) (k l : (iSupOpensCover U).I₀) :
    pullback.fst ((iSupOpensCover U).f k) ((iSupOpensCover U).f l) ≫ c k =
      pullback.snd ((iSupOpensCover U).f k) ((iSupOpensCover U).f l) ≫ c l := by
  have hp := isPullback_opens_inf_le (le_iSup U k) (le_iSup U l)
  change pullback.fst (X'.homOfLE (le_iSup U k)) (X'.homOfLE (le_iSup U l)) ≫ c k =
    pullback.snd (X'.homOfLE (le_iSup U k)) (X'.homOfLE (le_iSup U l)) ≫ c l
  rw [← hp.isoPullback_inv_fst, ← hp.isoPullback_inv_snd, Category.assoc, Category.assoc,
    hc k l]

/-- **The morphism glued from a family of lifts agreeing on pairwise intersections.** For a
family of morphisms `c k : V_k ⟶ Y'` whose restrictions to `V_k ⊓ V_l` agree there is a unique
morphism `⨆ V_k ⟶ Y'` restricting to each of them; this is it. -/
def glueCompatibleLifts (U : K → X'.Opens) (c : ∀ k, (U k).toScheme ⟶ Y')
    (hc : ∀ k l, X'.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ c k =
      X'.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ c l) :
    (iSup U).toScheme ⟶ Y' :=
  (iSupOpensCover U).glueMorphisms c (pullback_condition_of_inf U c hc)

/-- **The glued morphism restricts to the given one on each member of the family**, in the
spelling of the cover. -/
theorem f_glueCompatibleLifts (U : K → X'.Opens) (c : ∀ k, (U k).toScheme ⟶ Y')
    (hc : ∀ k l, X'.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ c k =
      X'.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ c l) (k : (iSupOpensCover U).I₀) :
    (iSupOpensCover U).f k ≫ glueCompatibleLifts U c hc = c k :=
  (iSupOpensCover U).ι_glueMorphisms c (pullback_condition_of_inf U c hc) k

/-- **The glued morphism restricts to the given one on each member of the family.** -/
theorem homOfLE_glueCompatibleLifts (U : K → X'.Opens) (c : ∀ k, (U k).toScheme ⟶ Y')
    (hc : ∀ k l, X'.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ c k =
      X'.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ c l) (k : K) :
    X'.homOfLE (le_iSup U k) ≫ glueCompatibleLifts U c hc = c k :=
  f_glueCompatibleLifts U c hc k

/-- **Condition (1) of [Stacks Project, Tag 04FI] is local on `X'`.** A morphism glued from
morphisms over `S` is a morphism over `S`, since both sides of the equation defining that are
determined by their restrictions to the cover. -/
theorem glueCompatibleLifts_over (hl : ∀ k, IsCompatibleLift pX' pY' a A (U k) (c k))
    (hc : ∀ k l, X'.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ c k =
      X'.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ c l) :
    glueCompatibleLifts U c hc ≫ pY' = (iSup U).ι ≫ pX' := by
  refine (iSupOpensCover U).hom_ext _ _ (fun k => ?_)
  rw [← Category.assoc, ← Category.assoc, f_glueCompatibleLifts]
  exact (hl k).1.trans (by simp [iSupOpensCover, openCoverOfOpens])

/-- **Condition (2) of [Stacks Project, Tag 04FI] is local on `X'`.** A morphism glued from lifts
of `a` restricts to `a` on `i⁻¹(⨆ V_k)`, since both sides of that equation are determined by
their restrictions to the cover of `i⁻¹(⨆ V_k)` by the opens `i⁻¹V_k`. -/
theorem glueCompatibleLifts_restrict (hl : ∀ k, IsCompatibleLift pX' pY' a A (U k) (c k))
    (hc : ∀ k l, X'.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ c k =
      X'.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ c l) :
    i ∣_ iSup U ≫ glueCompatibleLifts U c hc = ((i ⁻¹ᵁ iSup U).ι ≫ a) ≫ j := by
  refine hom_ext_of_opens (fun k => i ⁻¹ᵁ U k) (fun k => i.preimage_mono (le_iSup U k))
    (exists_mem_preimage_iSup i U) _ _ (fun k => ?_)
  obtain ⟨-, hk2, -⟩ := hl k
  rw [← Category.assoc, ← morphismRestrict_homOfLE i (U k) (iSup U) (le_iSup U k),
    Category.assoc, homOfLE_glueCompatibleLifts, hk2, ← Category.assoc,
    homOfLE_comp_ι_comp a (le_iSup U k)]

/-- **Cancelling isomorphisms on both sides of an equation.** Two morphisms that become equal
after the same two isomorphisms are prefixed and the same isomorphism is appended were already
equal. Stated so that the four large module terms of
`Stacks.Thickenings.glueCompatibleLifts_conormal` are written once. -/
private theorem eq_of_isIso_comp {C : Type*} [Category C] {A₀ A₁ A₂ B₀ B₁ : C}
    (e : A₀ ⟶ A₁) (f : A₁ ⟶ A₂) (m : B₀ ⟶ B₁) (he : IsIso e) (hf : IsIso f) (hm : IsIso m)
    {x y : A₂ ⟶ B₀} (h : e ≫ f ≫ x ≫ m = e ≫ f ≫ y ≫ m) : x = y := by
  have := he
  have := hf
  have := hm
  exact (cancel_mono m).1 ((cancel_epi f).1 ((cancel_epi e).1 h))

/-- **The restriction rule for the map of conormal sheaves induced by a glued lift.** Over the
member `V_k` of the family the induced map of the glued lift, read through the comparison
isomorphisms and the canonical map of the restriction square, is the restriction of `A` to
`i⁻¹V_k`.

The induced map restricts by `Stacks.Immersion.immersionConormalSheafMap_morphismRestrict`; the
transport `Stacks.Immersion.immersionConormalSheafMap_congr` replaces the two edges of the square
by `ι_{i⁻¹V_k} ≫ a` and by the lift `c k` itself, after which the third condition for `c k`
applies. -/
private theorem comp_conormal_glueCompatibleLifts
    (hl : ∀ k, IsCompatibleLift pX' pY' a A (U k) (c k))
    (hc : ∀ k l, X'.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ c k =
      X'.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ c l) (k : K) :
    eqToHom (congrArg (fun p : (i ⁻¹ᵁ U k).toScheme ⟶ Y =>
          (modulePullback p.toLRSHom.toShHom).obj (immersionConormalSheaf j))
        (homOfLE_comp_ι_comp a (le_iSup U k)).symm) ≫
      (modulePullbackComp (X.homOfLE (i.preimage_mono (le_iSup U k))).toLRSHom.toShHom
          ((i ⁻¹ᵁ iSup U).ι ≫ a).toLRSHom.toShHom).hom.app (immersionConormalSheaf j) ≫
        (modulePullback (X.homOfLE (i.preimage_mono (le_iSup U k))).toLRSHom.toShHom).map
            (immersionConormalSheafMap (i ∣_ iSup U) j ((i ⁻¹ᵁ iSup U).ι ≫ a)
              (glueCompatibleLifts U c hc)
              (toShHom_square (glueCompatibleLifts_restrict hl hc))) ≫
          immersionConormalSheafMap (i ∣_ U k) (i ∣_ iSup U)
            (X.homOfLE (i.preimage_mono (le_iSup U k))) (X'.homOfLE (le_iSup U k))
            (toShHom_square (morphismRestrict_homOfLE i (U k) (iSup U) (le_iSup U k))) =
      restrictConormalSheafMap a A (U k) := by
  obtain ⟨-, hk2, hk3⟩ := hl k
  refine Eq.trans (congrArg (fun z => eqToHom (congrArg
        (fun p : (i ⁻¹ᵁ U k).toScheme ⟶ Y =>
          (modulePullback p.toLRSHom.toShHom).obj (immersionConormalSheaf j))
        (homOfLE_comp_ι_comp a (le_iSup U k)).symm) ≫ z)
      (immersionConormalSheafMap_morphismRestrict i (le_iSup U k) ((i ⁻¹ᵁ iSup U).ι ≫ a)
        (glueCompatibleLifts U c hc) (glueCompatibleLifts_restrict hl hc)).symm) ?_
  exact (immersionConormalSheafMap_congr (i ∣_ U k) j
      (homOfLE_comp_ι_comp a (le_iSup U k)) (homOfLE_glueCompatibleLifts U c hc k)
      (toShHom_square (square_comp (morphismRestrict_homOfLE i (U k) (iSup U) (le_iSup U k))
        (glueCompatibleLifts_restrict hl hc)))
      (toShHom_square hk2)).symm.trans hk3

/-- **Condition (3) of [Stacks Project, Tag 04FI] is local on `X'`, over one member of the
family.** The pullbacks along `ρ : i⁻¹V_k ⟶ i⁻¹(⨆ V_l)` of the two sides of condition (3) over
`⨆ V_l` agree.

Both sides restrict by the same rule — the induced map by
`Stacks.Thickenings.comp_conormal_glueCompatibleLifts`, the restriction of `A` by
`Stacks.Thickenings.restrictConormalSheafMap_homOfLE` — and the factors of that rule other than
`ρ^*` are isomorphisms, the outer one by
`Stacks.Immersion.isIso_immersionConormalSheafMap_homOfLE`. -/
private theorem modulePullback_conormal_glueCompatibleLifts
    (hl : ∀ k, IsCompatibleLift pX' pY' a A (U k) (c k))
    (hc : ∀ k l, X'.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ c k =
      X'.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ c l) (k : K) :
    (modulePullback (X.homOfLE (i.preimage_mono (le_iSup U k))).toLRSHom.toShHom).map
        (immersionConormalSheafMap (i ∣_ iSup U) j ((i ⁻¹ᵁ iSup U).ι ≫ a)
          (glueCompatibleLifts U c hc)
          (toShHom_square (glueCompatibleLifts_restrict hl hc))) =
      (modulePullback (X.homOfLE (i.preimage_mono (le_iSup U k))).toLRSHom.toShHom).map
        (restrictConormalSheafMap a A (iSup U)) :=
  eq_of_isIso_comp
    (eqToHom (congrArg (fun p : (i ⁻¹ᵁ U k).toScheme ⟶ Y =>
        (modulePullback p.toLRSHom.toShHom).obj (immersionConormalSheaf j))
      (homOfLE_comp_ι_comp a (le_iSup U k)).symm))
    ((modulePullbackComp (X.homOfLE (i.preimage_mono (le_iSup U k))).toLRSHom.toShHom
      ((i ⁻¹ᵁ iSup U).ι ≫ a).toLRSHom.toShHom).hom.app (immersionConormalSheaf j))
    (immersionConormalSheafMap (i ∣_ U k) (i ∣_ iSup U)
      (X.homOfLE (i.preimage_mono (le_iSup U k))) (X'.homOfLE (le_iSup U k))
      (toShHom_square (morphismRestrict_homOfLE i (U k) (iSup U) (le_iSup U k))))
    inferInstance
    ((modulePullbackComp (X.homOfLE (i.preimage_mono (le_iSup U k))).toLRSHom.toShHom
      ((i ⁻¹ᵁ iSup U).ι ≫ a).toLRSHom.toShHom).app (immersionConormalSheaf j)).isIso_hom
    (isIso_immersionConormalSheafMap_homOfLE i (le_iSup U k))
    ((comp_conormal_glueCompatibleLifts hl hc k).trans
      (restrictConormalSheafMap_homOfLE a A (le_iSup U k)))

/-- **Condition (3) of [Stacks Project, Tag 04FI] is local on `X'`.** The map of conormal sheaves
induced by a glued lift is the restriction of `A`, given that this holds for each member of the
family.

By `Stacks.Thickenings.modulePullback_conormal_glueCompatibleLifts` the two sides agree after
pullback along each `ρ : i⁻¹V_k ⟶ i⁻¹(⨆ V_l)`, and those pullbacks jointly determine a morphism
of sheaves of modules by
`RingedSpaceModuleAdjunction.modulePullback_homOfLE_map_injective`. -/
theorem glueCompatibleLifts_conormal (hl : ∀ k, IsCompatibleLift pX' pY' a A (U k) (c k))
    (hc : ∀ k l, X'.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ c k =
      X'.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ c l) :
    immersionConormalSheafMap (i ∣_ iSup U) j ((i ⁻¹ᵁ iSup U).ι ≫ a)
        (glueCompatibleLifts U c hc)
        (toShHom_square (glueCompatibleLifts_restrict hl hc)) =
      restrictConormalSheafMap a A (iSup U) :=
  modulePullback_homOfLE_map_injective (B := i ⁻¹ᵁ iSup U) (fun k => i ⁻¹ᵁ U k)
    (fun k => i.preimage_mono (le_iSup U k)) (exists_mem_preimage_iSup i U)
    (modulePullback_conormal_glueCompatibleLifts hl hc)

/-- **The glued morphism is a compatible lift**, so the three conditions of
[Stacks Project, Tag 04FI] are local on `X'`. -/
theorem isCompatibleLift_glueCompatibleLifts
    (hl : ∀ k, IsCompatibleLift pX' pY' a A (U k) (c k))
    (hc : ∀ k l, X'.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ c k =
      X'.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ c l) :
    IsCompatibleLift pX' pY' a A (iSup U) (glueCompatibleLifts U c hc) :=
  ⟨glueCompatibleLifts_over hl hc, glueCompatibleLifts_restrict hl hc,
    glueCompatibleLifts_conormal hl hc⟩

/-- **[Stacks Project, Tag 04FH].** For a scheme `S`, immersions `i : X ⟶ X'` and `j : Y ⟶ Y'`, a
morphism `a : X ⟶ Y` and a map `A : a^* 𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}`, the rule assigning to an open `V`
of `X'` the set of morphisms `V ⟶ Y'` over `S` restricting to `a` on `i⁻¹V` and inducing the
restriction of `A` there is a **sheaf of sets** on `X'`.

The proof is the unique-gluing form of the sheaf condition. A compatible family of lifts glues to
a morphism by `Stacks.Thickenings.glueCompatibleLifts`, that morphism is again a compatible lift
by `Stacks.Thickenings.isCompatibleLift_glueCompatibleLifts`, and a lift over the union is
determined by its restrictions to the cover. -/
@[stacks 04FH]
theorem isSheaf_compatibleLiftsPresheaf (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) :
    (compatibleLiftsPresheaf pX' pY' a A).IsSheaf := by
  refine TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types _ (fun K U sf hsf => ?_)
  have hc : ∀ k l, X'.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ (sf k).1 =
      X'.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ (sf l).1 :=
    fun k l => congrArg Subtype.val (hsf k l)
  refine ⟨⟨glueCompatibleLifts U (fun k => (sf k).1) hc,
    isCompatibleLift_glueCompatibleLifts (fun k => (sf k).2) hc⟩, fun k => ?_, fun s hs => ?_⟩
  · exact Subtype.ext (homOfLE_glueCompatibleLifts U (fun k => (sf k).1) hc k)
  · refine Subtype.ext ((iSupOpensCover U).hom_ext _ _ (fun k => ?_))
    exact (congrArg Subtype.val (hs k)).trans
      (homOfLE_glueCompatibleLifts U (fun k => (sf k).1) hc k).symm

/-- **[Stacks Project, Tag 04FH] in the setting in which it is stated**, where `i` and `j` are
first-order thickenings over `S` in the sense of [Stacks Project, Tag 04EX]. -/
theorem isSheaf_firstOrderCompatibleLiftsPresheaf {i : X ⟶ X'} {j : Y ⟶ Y'}
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j) (pX' : X' ⟶ S)
    (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : letI := hi.1; letI := hj.1;
      (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
        immersionConormalSheaf i) :
    letI := hi.1
    letI := hj.1
    (compatibleLiftsPresheaf pX' pY' a A).IsSheaf :=
  let := hi.1
  let := hj.1
  isSheaf_compatibleLiftsPresheaf pX' pY' a A

end Stacks.Thickenings

end
