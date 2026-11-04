module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.ClosedSubspaceScheme
public import StacksCore.Tactic.StacksAttribute

/-!
# Immersions and fibre products of schemes

Closed, open and locally closed immersions of schemes are preserved by base change: if
`f : X ⟶ S` is an immersion of one of these kinds and `g : Y ⟶ S` is any morphism, then
`X ×_S Y ⟶ Y` is an immersion of the same kind. When `f` is a closed immersion cut out by the
sheaf of ideals `ℐ ⊆ 𝒪_S`, the base change `X ×_S Y ⟶ Y` is cut out by the inverse-image ideal
`Im(g^* ℐ ⟶ 𝒪_Y)`.

The three stability assertions are available in Mathlib in their stronger, choice-free
base-change form, which applies to either projection of an arbitrary cartesian square rather than
to a chosen pullback, so this file records the identifications rather than restating them. The
identification of the ideal is proved here.

## Main results

The source's three stability assertions are
`AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange`,
`AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange` and
`AlgebraicGeometry.IsImmersion.isStableUnderBaseChange`.

* `Stacks.ClosedImmersion.existsUnique_idealSheaf_pullbackSnd_iso_pullbackIdeal`: **the ideal
  assertion of part (1)**, the ideal sheaf of `X ×_S Y ⟶ Y` is the inverse-image ideal of `ℐ`
  along `g`, by a unique isomorphism compatible with the two inclusions into `𝒪_Y`.

## Implementation notes

The ideal assertion is proved by exhibiting the closed subspace of `Y` cut out by the
inverse-image ideal as the fibre product. That closed subspace is the fibre product in locally
ringed spaces by [Stacks, Tag 01HQ] (`Stacks.ClosedImmersion.restrictedMap_isPullback`), and it
is a scheme by [Stacks, Tag 01IN] (`Stacks.ClosedImmersion.closedSubscheme`); since
`AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace` is faithful and reflects the relevant
limits, the same square is a fibre square of schemes, so it is the chosen pullback. The ideal
sheaf of the projection is then read off from
`Stacks.ClosedImmersion.ClosedSubspaceData.idealIso`, transported along the identification of the
two sources by `Stacks.ClosedImmersion.idealSheafCompIso`.

The composite is assembled through a purely categorical bookkeeping lemma, stated for an
arbitrary category, rather than by rewriting in the composite directly: the objects
involved are sheaves of modules over structure sheaves spelled in two definitionally equal ways,
so a `rw` motive over them is not type-correct at the elaborator's implicit transparency, and
each rewrite would have to see through that.

## References

* [Stacks Project, Tag 01HQ](https://stacks.math.columbia.edu/tag/01HQ)
* [Stacks Project, Tag 01IN](https://stacks.math.columbia.edu/tag/01IN)
* [Stacks Project, Tag 01JU](https://stacks.math.columbia.edu/tag/01JU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

add_to_stacks 01JU "part (1): closed immersion"
  AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
add_to_stacks 01JU "part (2): open immersion"
  AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange
add_to_stacks 01JU "part (3): immersion"
  AlgebraicGeometry.IsImmersion.isStableUnderBaseChange

namespace Stacks.ClosedImmersion

/-! ### A composition identity -/

/-- A purely categorical bookkeeping step: a morphism factored as `a ≫ b ≫ c`, composed with
`t`, is `t₃` as soon as the three composites cancel in turn. Stated for an arbitrary category so
that the associativity shuffling happens away from the sheaves of modules it is applied to. -/
private theorem comp_eq_of_three_factors {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ : C}
    {x : A₀ ⟶ A₃} (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (t : A₃ ⟶ A₄)
    {t₁ : A₂ ⟶ A₄} {t₂ : A₁ ⟶ A₄} {t₃ : A₀ ⟶ A₄} (hx : x = a ≫ b ≫ c) (h₁ : c ≫ t = t₁)
    (h₂ : b ≫ t₁ = t₂) (h₃ : a ≫ t₂ = t₃) :
    x ≫ t = t₃ := by
  rw [hx, Category.assoc, Category.assoc, h₁, h₂, h₃]

/-! ### The inverse-image ideal depends only on the sheaf of ideals -/

/-- The compatibility making the two inverse-image ideal maps the two sides of a square: the
pullback of an isomorphism of sheaves of ideals carries one to the other. -/
private theorem pullbackIdealMap_compat {W P : LocallyRingedSpace.{u}} (h : W ⟶ P)
    (I J : SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing P.toRingedSpace))
    (j : J ⟶ SheafOfModules.unit (structureSheafRing P.toRingedSpace))
    (e : I ≅ J) (he : e.hom ≫ j = i) :
    (modulePullback h.toShHom).map e.hom ≫ pullbackIdealMap h J j = pullbackIdealMap h I i := by
  dsimp [pullbackIdealMap]
  rw [← he, Functor.map_comp]
  rfl

/-- The square of `pullbackIdealMap_compat`, read as an isomorphism in the arrow category. -/
private def pullbackIdealArrowIso {W P : LocallyRingedSpace.{u}} (h : W ⟶ P)
    (I J : SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing P.toRingedSpace))
    (j : J ⟶ SheafOfModules.unit (structureSheafRing P.toRingedSpace))
    (e : I ≅ J) (he : e.hom ≫ j = i) :
    Arrow.mk (pullbackIdealMap h I i) ≅ Arrow.mk (pullbackIdealMap h J j) :=
  Arrow.isoMk (asIso ((modulePullback h.toShHom).map e.hom)) (Iso.refl _)
    (by simpa using pullbackIdealMap_compat h I J i j e he)

/-- **Transport of the inverse-image ideal along an isomorphism of sheaves of ideals.** Two
modules identified compatibly with their maps to `𝒪_P` have the same inverse-image ideal along a
morphism `h : W ⟶ P` of locally ringed spaces. -/
private def pullbackIdealIsoOfCompat {W P : LocallyRingedSpace.{u}} (h : W ⟶ P)
    (I J : SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing P.toRingedSpace))
    (j : J ⟶ SheafOfModules.unit (structureSheafRing P.toRingedSpace))
    (e : I ≅ J) (he : e.hom ≫ j = i) :
    pullbackIdeal h I i ≅ pullbackIdeal h J j :=
  Abelian.im.mapIso (pullbackIdealArrowIso h I J i j e he)

/-- `pullbackIdealIsoOfCompat` commutes with the two inclusions into `𝒪_W`. Those inclusions are
monomorphisms, so this determines the isomorphism. -/
private theorem pullbackIdealIsoOfCompat_hom_inclusion {W P : LocallyRingedSpace.{u}}
    (h : W ⟶ P)
    (I J : SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing P.toRingedSpace))
    (j : J ⟶ SheafOfModules.unit (structureSheafRing P.toRingedSpace))
    (e : I ≅ J) (he : e.hom ≫ j = i) :
    (pullbackIdealIsoOfCompat h I J i j e he).hom ≫ pullbackIdealInclusion h J j =
      pullbackIdealInclusion h I i := by
  show Abelian.im.map (pullbackIdealArrowIso h I J i j e he).hom ≫
    Abelian.image.ι (pullbackIdealMap h J j) = Abelian.image.ι (pullbackIdealMap h I i)
  rw [Abelian.im_map]
  simp [pullbackIdealArrowIso, Abelian.im]

/-! ### The base change is the closed subspace of the inverse-image ideal -/

/-- **The fibre product of a closed immersion is the closed subspace of the inverse-image
ideal.** If the source of the closed immersion `f` is, over `S`, the closed subspace cut out by
`j₀ : J₀ ⟶ 𝒪_S`, then the chosen pullback `X ×_S Y` is, over `Y`, the closed subspace cut out by
the inverse-image ideal of `j₀` along `g`.

The corresponding square of locally ringed spaces is cartesian by [Stacks, Tag 01HQ], and all
four of its objects are schemes by [Stacks, Tag 01IN], so faithfulness of
`AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace` upgrades it to a cartesian square of
schemes. -/
private theorem exists_iso_pullbackSnd_pullbackClosedSubspace {X Y S : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) (J₀ : SheafOfModules.{u} (structureSheafRing S.toLocallyRingedSpace.toRingedSpace))
    (j₀ : J₀ ⟶ SheafOfModules.unit (structureSheafRing S.toLocallyRingedSpace.toRingedSpace))
    [Mono j₀]
    (hJ₀ : Nonempty (SheafOfModules.LocalGeneratorsData.{u} J₀))
    (zL : X.toLocallyRingedSpace ≅ (closedSubspace S.toLocallyRingedSpace J₀ j₀ hJ₀).space)
    (hzL : zL.hom ≫ (closedSubspace S.toLocallyRingedSpace J₀ j₀ hJ₀).inclusion = f.toLRSHom) :
    ∃ ε : (pullback f g).toLocallyRingedSpace ≅
        (pullbackClosedSubspace g.toLRSHom J₀ j₀ hJ₀).space,
      (pullback.snd f g).toLRSHom =
        ε.hom ≫ (pullbackClosedSubspace g.toLRSHom J₀ j₀ hJ₀).inclusion := by
  let Z : Scheme.{u} := closedSubscheme S J₀ j₀ hJ₀
  let zι : Z ⟶ S := closedSubschemeInclusion S J₀ j₀ hJ₀
  let A : Scheme.{u} := closedSubscheme Y (pullbackIdeal g.toLRSHom J₀ j₀)
    (pullbackIdealInclusion g.toLRSHom J₀ j₀)
    (pullbackIdeal_locallyGenerated g.toLRSHom J₀ j₀ hJ₀)
  let aι : A ⟶ Y := closedSubschemeInclusion Y (pullbackIdeal g.toLRSHom J₀ j₀)
    (pullbackIdealInclusion g.toLRSHom J₀ j₀)
    (pullbackIdeal_locallyGenerated g.toLRSHom J₀ j₀ hJ₀)
  let zLR : Scheme.forgetToLocallyRingedSpace.obj X ≅ Scheme.forgetToLocallyRingedSpace.obj Z :=
    zL
  let kLR : Scheme.forgetToLocallyRingedSpace.obj A ⟶ Scheme.forgetToLocallyRingedSpace.obj Z :=
    restrictedMap g.toLRSHom J₀ j₀ hJ₀
  let z : X ≅ Z := Scheme.forgetToLocallyRingedSpace.preimageIso zLR
  let k : A ⟶ Z := Scheme.forgetToLocallyRingedSpace.preimage kLR
  have hz1 : Scheme.forgetToLocallyRingedSpace.map z.hom = zLR.hom :=
    Scheme.forgetToLocallyRingedSpace.map_preimage _
  have hk1 : Scheme.forgetToLocallyRingedSpace.map k = kLR :=
    Scheme.forgetToLocallyRingedSpace.map_preimage _
  have hz : z.hom ≫ zι = f := by
    refine Scheme.forgetToLocallyRingedSpace.map_injective ?_
    rw [Scheme.forgetToLocallyRingedSpace.map_comp, hz1]
    exact hzL
  have hA : IsPullback k aι zι g := by
    refine IsPullback.of_map_of_faithful Scheme.forgetToLocallyRingedSpace ?_
    rw [hk1]
    exact (restrictedMap_isPullback g.toLRSHom J₀ j₀ hJ₀).flip
  have hP : IsPullback (pullback.fst f g ≫ z.hom) (pullback.snd f g) zι g := by
    refine (IsPullback.of_hasPullback f g).of_iso (Iso.refl _) z (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) ?_ (by simp)
    simpa using hz.symm
  have hePA : (hP.isoPullback ≪≫ hA.isoPullback.symm).hom ≫ aι = pullback.snd f g := by
    simp
  exact ⟨Scheme.forgetToLocallyRingedSpace.mapIso (hP.isoPullback ≪≫ hA.isoPullback.symm),
    (congrArg (fun q : pullback f g ⟶ Y => q.toLRSHom) hePA).symm⟩

/-! ### The ideal sheaf of the base change -/

/-- **The ideal sheaf of the base change, for the presentation used to build the fibre
product.** Composing the identification of the fibre product with the closed subspace of the
inverse-image ideal, the transport of the ideal sheaf along it, and the canonical identification
of the ideal sheaf of a closed subspace. -/
private theorem exists_idealSheaf_pullbackSnd_iso {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (J₀ : SheafOfModules.{u} (structureSheafRing S.toLocallyRingedSpace.toRingedSpace))
    (j₀ : J₀ ⟶ SheafOfModules.unit (structureSheafRing S.toLocallyRingedSpace.toRingedSpace))
    [Mono j₀]
    (hJ₀ : Nonempty (SheafOfModules.LocalGeneratorsData.{u} J₀))
    (zL : X.toLocallyRingedSpace ≅ (closedSubspace S.toLocallyRingedSpace J₀ j₀ hJ₀).space)
    (hzL : zL.hom ≫ (closedSubspace S.toLocallyRingedSpace J₀ j₀ hJ₀).inclusion = f.toLRSHom) :
    ∃ φ : idealSheaf (pullback.snd f g).toLRSHom.toShHom ≅ pullbackIdeal g.toLRSHom J₀ j₀,
      φ.hom ≫ pullbackIdealInclusion g.toLRSHom J₀ j₀ =
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom (pullback.snd f g).toLRSHom.toShHom)) := by
  obtain ⟨ε, hε⟩ := exists_iso_pullbackSnd_pullbackClosedSubspace f g J₀ j₀ hJ₀ zL hzL
  refine ⟨idealSheafCongr (congrArg LocallyRingedSpace.Hom.toShHom hε) ≪≫
    idealSheafCompIso ε (pullbackClosedSubspace g.toLRSHom J₀ j₀ hJ₀).inclusion ≪≫
      (pullbackClosedSubspace g.toLRSHom J₀ j₀ hJ₀).idealIso.symm, ?_⟩
  exact comp_eq_of_three_factors _ _ _ _ rfl
    ((Iso.inv_comp_eq _).2 (pullbackClosedSubspace g.toLRSHom J₀ j₀ hJ₀).idealIso_compat.symm)
    (idealSheafCompIso_hom_kernel_ι ε
      (pullbackClosedSubspace g.toLRSHom J₀ j₀ hJ₀).inclusion)
    (idealSheafCongr_hom_kernel_ι (congrArg LocallyRingedSpace.Hom.toShHom hε))

/-- **Stacks Project, Tag 01JU, part (1).** Let `f : X ⟶ S` be a closed immersion of schemes
corresponding to the sheaf of ideals `i : I ⟶ 𝒪_S`, and let `g : Y ⟶ S` be any morphism of
schemes. Then the base change `X ×_S Y ⟶ Y`, which is a closed immersion by
`AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange`, corresponds to the inverse-image
ideal `Im(g^* I ⟶ 𝒪_Y)`: its ideal sheaf is that ideal, by a unique isomorphism compatible with
the two inclusions into `𝒪_Y`. -/
@[stacks 01JU "part (1): inverse-image ideal"]
theorem existsUnique_idealSheaf_pullbackSnd_iso_pullbackIdeal {X Y S : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) [hcl : AlgebraicGeometry.IsClosedImmersion f]
    (I : SheafOfModules.{u} (structureSheafRing S.toLocallyRingedSpace.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing S.toLocallyRingedSpace.toRingedSpace))
    (e : I ≅ idealSheaf f.toLRSHom.toShHom)
    (he : e.hom ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom f.toLRSHom.toShHom)) = i) :
    ∃! e' : idealSheaf (pullback.snd f g).toLRSHom.toShHom ≅ pullbackIdeal g.toLRSHom I i,
      e'.hom ≫ pullbackIdealInclusion g.toLRSHom I i =
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom (pullback.snd f g).toLRSHom.toShHom)) := by
  have hf : IsClosedImmersion f.toLRSHom.toShHom :=
    ((Stacks.AlgebraicGeometry.ClosedImmersionTFAE.closedImmersion_tfae f).out 1 6).mp hcl
  have hm : Mono (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom f.toLRSHom.toShHom))) := equalizer.ι_mono
  obtain ⟨zL, hzL, -⟩ := existsUnique_iso_closedSubspace f.toLRSHom
  obtain ⟨φ, hφ⟩ := exists_idealSheaf_pullbackSnd_iso f g (idealSheaf f.toLRSHom.toShHom)
    (kernel.ι _) hf.kernel_locallyGenerated zL hzL
  obtain ⟨e', he'⟩ : ∃ e' : idealSheaf (pullback.snd f g).toLRSHom.toShHom ≅
        pullbackIdeal g.toLRSHom I i,
      e'.hom ≫ pullbackIdealInclusion g.toLRSHom I i =
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom (pullback.snd f g).toLRSHom.toShHom)) :=
    ⟨φ ≪≫ (pullbackIdealIsoOfCompat g.toLRSHom I (idealSheaf f.toLRSHom.toShHom) i
        (kernel.ι _) e he).symm,
      (Category.assoc _ _ _).trans ((congrArg (fun z ↦ φ.hom ≫ z) ((Iso.inv_comp_eq _).2
        (pullbackIdealIsoOfCompat_hom_inclusion g.toLRSHom I (idealSheaf f.toLRSHom.toShHom) i
          (kernel.ι _) e he).symm)).trans hφ)⟩
  exact ⟨e', he', fun q hq ↦ Iso.ext ((cancel_mono (pullbackIdealInclusion g.toLRSHom I i)).1
    (hq.trans he'.symm))⟩

end Stacks.ClosedImmersion

end
