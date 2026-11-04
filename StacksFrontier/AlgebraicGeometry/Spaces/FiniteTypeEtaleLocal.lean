module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberQuasicoherence

/-!
# Finite type is local for the étale topology of an algebraic space

Let `gᵢ : Yᵢ ⟶ X` be a family of étale morphisms of algebraic spaces whose charts are cover dense
in the small étale site of `X` — for instance an étale covering of `X`.  This file proves that an
`𝒪_X`-module whose étale restriction to every `Yᵢ` is of finite type is itself of finite type.
It is the finite type companion of
`AlgebraicGeometry.Space.QuasiCoherentDescent.isQuasicoherentOnSite_of_forall_etaleModulePullback`.

## Main results

* `AlgebraicGeometry.Space.generatingSectionsOverPostcomp`: generating sections of the restriction
  of `M|_Y` to a chart `V` of `Y` are generating sections of the restriction of `M` to the
  composite chart of `X`, indexed by the same type.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isFiniteType_of_forall_etaleModulePullback`:
  finite type is detected on a cover-dense family of étale morphisms.

## Implementation notes

The transfer of generating sections goes through the slice equivalence
`AlgebraicGeometry.Space.SmallEtale.postcompOverEquivalence` exactly as the transfer of global
presentations in `AlgebraicGeometry.Space.hasGlobalPresentation_over_postcomp_iff` does: the two
restrictions are identified by the pushforward along the equivalence, and
`SheafOfModules.GeneratingSections.map` carries generating sections along the inverse
pushforward, which preserves colimits because it is an equivalence.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits SheafOfModules

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Generating sections transfer from a chart of `Y` to the composite chart of `X`.**  For an
étale `f : Y ⟶ X`, an `𝒪_X`-module `M` and a chart `V` of `Y`, generating sections of the
restriction of `M|_Y` to `V` give generating sections of the restriction of `M` to the composite
chart `f ∘ V`, indexed by the same type. -/
def generatingSectionsOverPostcomp {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C)
    (σ : (((etaleModulePullback B S hS f hf).obj M).over V).GeneratingSections) :
    (M.over ((ringedSitePostcomp B S hS f hf).obj V)).GeneratingSections :=
  let E : Over V ≌ Over ((ringedSitePostcomp B S hS f hf).obj V) :=
    SmallEtale.postcompOverEquivalence B S hS f hf V
  have hc1 : E.functor.IsContinuous ((smallEtaleRingedSite B S hS Y.1 Y.2).J.over V)
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over
        ((ringedSitePostcomp B S hS f hf).obj V)) :=
    SmallEtale.isContinuous_overPostcomp B S hS f hf V
  have hc2 : E.inverse.IsContinuous
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over
        ((ringedSitePostcomp B S hS f hf).obj V))
      ((smallEtaleRingedSite B S hS Y.1 Y.2).J.over V) :=
    SmallEtale.isContinuous_postcompOverInverse B S hS f hf V
  let RY := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
  let RX := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  let φ : RY.over V ⟶ (E.functor.sheafPushforwardContinuous RingCat.{u}
      ((smallEtaleRingedSite B S hS Y.1 Y.2).J.over V)
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over
        ((ringedSitePostcomp B S hS f hf).obj V))).obj
      (RX.over ((ringedSitePostcomp B S hS f hf).obj V)) := 𝟙 _
  let ψ : RX.over ((ringedSitePostcomp B S hS f hf).obj V) ⟶
      (E.inverse.sheafPushforwardContinuous RingCat.{u}
        ((smallEtaleRingedSite B S hS X.1 X.2).J.over
          ((ringedSitePostcomp B S hS f hf).obj V))
        ((smallEtaleRingedSite B S hS Y.1 Y.2).J.over V)).obj (RY.over V) := 𝟙 _
  have H₁ : Functor.whiskerRight (NatTrans.op E.counit)
      (RX.over ((ringedSitePostcomp B S hS f hf).obj V)).obj =
      ψ.hom ≫ E.inverse.op.whiskerLeft φ.hom := by
    ext : 2
    exact rfl
  have H₂ : φ.hom ≫ E.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op E.unit) (RY.over V).obj = 𝟙 (RY.over V).obj := by
    ext : 2
    exact rfl
  let e₀ := SheafOfModules.pushforwardPushforwardEquivalence.{u} E φ ψ H₁ H₂
  let F₀ := SheafOfModules.pushforward.{u} φ
  let G₀ := SheafOfModules.pushforward.{u} ψ
  have hGadj : G₀.IsLeftAdjoint := e₀.symm.isLeftAdjoint_functor
  have hGcol : PreservesColimitsOfSize.{u, u} G₀ :=
    (Adjunction.ofIsLeftAdjoint G₀).leftAdjoint_preservesColimits
  let key : F₀.obj (M.over ((ringedSitePostcomp B S hS f hf).obj V)) ≅
      ((etaleModulePullback B S hS f hf).obj M).over V :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext x; rfl))
  let η : SheafOfModules.unit (RX.over ((ringedSitePostcomp B S hS f hf).obj V)) ≅
      G₀.obj (SheafOfModules.unit (RY.over V)) :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext; rfl))
  GeneratingSections.equivOfIso
    (e₀.unitIso.app (M.over ((ringedSitePostcomp B S hS f hf).obj V))).symm
    ((GeneratingSections.equivOfIso key.symm σ).map G₀ η)

/-- The generating sections transferred to the composite chart are finite when the given ones
are. -/
instance generatingSectionsOverPostcomp_isFiniteType {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C)
    (σ : (((etaleModulePullback B S hS f hf).obj M).over V).GeneratingSections)
    [σ.IsFiniteType] : (generatingSectionsOverPostcomp B S hS f hf M V σ).IsFiniteType :=
  ⟨inferInstanceAs (Finite σ.I)⟩

namespace QuasiCoherentDescent

variable {I : Type u} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-- **An `𝒪_X`-module whose étale restriction to every member of a cover-dense family is of
finite type is of finite type.** -/
theorem isFiniteType_of_forall_etaleModulePullback
    [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]
    (M : Modules.{u, u} B S hS X.1 X.2)
    (h : ∀ i, ((etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M).IsFiniteType) :
    M.IsFiniteType := by
  classical
  choose q hq using fun i =>
    SheafOfModules.IsFiniteType.exists_localGeneratorsData.{u}
      ((etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M)
  let J := Σ i : I, (q i).I
  let Z (z : J) : (smallEtaleRingedSite B S hS X.1 X.2).C :=
    (ringedSitePostcomp B S hS (f z.1) (hf z.1)).obj ((q z.1).X z.2)
  let gens (z : J) : (M.over (Z z)).GeneratingSections :=
    generatingSectionsOverPostcomp B S hS (f z.1) (hf z.1) M ((q z.1).X z.2)
      ((q z.1).generators z.2)
  refine ⟨⟨{ I := J, X := Z, coversTop := ?_, generators := gens }, ⟨fun z => ?_⟩⟩⟩
  · intro W
    refine (smallEtaleRingedSite B S hS X.1 X.2).J.transitive
      ((memberFunctor B S hS Yi f hf).is_cover_of_isCoverDense
        (SmallEtale.topology B S hS X.1) W) _ ?_
    intro W' g hg
    obtain ⟨⟨p, a, -, -⟩⟩ := hg
    have hpush := (SmallEtale.coverPreserving_smallEtalePostcomp B S hS (f p.1)
      (hf p.1)).cover_preserve ((q p.1).coversTop p.2)
    have hle : Sieve.functorPushforward (ringedSitePostcomp B S hS (f p.1) (hf p.1))
        (Sieve.ofObjects (q p.1).X p.2) ≤
        (Sieve.ofObjects Z ((ringedSitePostcomp B S hS (f p.1) (hf p.1)).obj p.2)) := by
      rintro T r ⟨Z₀, r₀, c, hr₀, rfl⟩
      obtain ⟨k, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff _ _).mp hr₀
      exact (Sieve.mem_ofObjects_iff _ _).2
        ⟨⟨p.1, k⟩, ⟨c ≫ (ringedSitePostcomp B S hS (f p.1) (hf p.1)).map b⟩⟩
    have hobj := (smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering hle hpush
    have hα := (smallEtaleRingedSite B S hS X.1 X.2).J.pullback_stable a hobj
    refine (smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering ?_ hα
    intro T b hb
    obtain ⟨k, ⟨c⟩⟩ := (Sieve.mem_ofObjects_iff _ _).mp hb
    exact (Sieve.mem_ofObjects_iff _ _).2 ⟨k, ⟨c⟩⟩
  · have := (hq z.1).isFiniteType z.2
    exact generatingSectionsOverPostcomp_isFiniteType B S hS (f z.1) (hf z.1) M _ _

end QuasiCoherentDescent

end AlgebraicGeometry.Space

end
