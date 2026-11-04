module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ProperOverBase.Functoriality
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekFunctorial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Composing proper-support direct images

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be separated morphisms locally of finite type in a big étale
site. The proper-support direct image `f_!` is a functor on abelian sheaves on the small étale
site, and iterating it along `f` and then `g` gives the same subsheaf of the direct image along
`f ≫ g` as `(f ≫ g)_!` does.

Both are subsheaves of the ordinary direct image along `f ≫ g`, once the latter is identified
with the iterated ordinary direct image by the canonical comparison of the small étale site
functors, so the agreement is recorded as an isomorphism whose square with the two
monomorphisms into the ordinary direct image commutes. Monicity makes that isomorphism unique,
and it is natural in the sheaf.

## Main definitions

* `AlgebraicGeometry.SmallEtale.properSupportFunctor`: proper-support direct image as a functor on
  abelian sheaves on the small étale site.

## Main results

* `AlgebraicGeometry.SmallEtale.properSupportSheaf_compIso`: the comparison isomorphism at a
  fixed sheaf, bundled with the commuting square that characterises it.
* `AlgebraicGeometry.SmallEtale.properSupportFunctor_compIso`: the same comparison as a natural
  isomorphism of functors, bundled with the identification of its components.

## Implementation notes

A section of the iterated proper-support direct image over a test object `W ⟶ Z` is a section
of `F` over `X ×_Z W` whose support is proper over `Y ×_Z W` and, being carried by the
projection to a proper closed subset of `Y ×_Z W`, is proper over `W`; conversely properness
over `W` of the support forces properness of its image in `Y ×_Z W`, because a closed subset
proper over the base is proper over any intermediate separated base. That is the content of
the sectionwise identification, and the isomorphism of sheaves is read off from it since both
sides are subsheaves of one sheaf.

## References

* [Stacks Project, Tag 0F50](https://stacks.math.columbia.edu/tag/0F50)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

/-- For morphisms `r : A ⟶ C` and `q : C ⟶ D` locally of finite type with `q` separated, a
closed subset `T` of `A` is proper over `D` along `r ≫ q` if and only if it is proper over `C`
along `r` and its image under `r` is closed and proper over `D` along `q`. -/
theorem properOver_comp_iff_image
    {A C D : Scheme.{u}} (r : A ⟶ C) (q : C ⟶ D)
    [LocallyOfFiniteType r] [LocallyOfFiniteType q] [IsSeparated q]
    (T : TopologicalSpace.Closeds A) :
    IsProperOver (r ≫ q) T ↔
      IsProperOver r T ∧
        ∃ hI : IsClosed (r.base '' (T : Set A)),
          IsProperOver q ⟨r.base '' (T : Set A), hI⟩ := by
  classical
  let I := Scheme.IdealSheafData.vanishingIdeal T
  constructor
  · intro hT
    have hR : IsProper (I.subschemeι ≫ r) := by
      have hcomp : IsProper ((I.subschemeι ≫ r) ≫ q) := by
        show IsProper (I.subschemeι ≫ (r ≫ q))
        exact hT
      exact IsProper.of_comp (I.subschemeι ≫ r) q
    have hImageClosed : IsClosed (r.base '' (T : Set A)) := by
      apply isClosed_image_of_isProperOver
        (r ≫ q) q r (by simp) T
      exact hT
    refine ⟨?_, hImageClosed, ?_⟩
    · show IsProper (I.subschemeι ≫ r)
      exact hR
    · exact isProperOver_image
        (r ≫ q) q r (by simp) T hT
  · rintro ⟨hR, hImageClosed, hImage⟩
    let J := Scheme.IdealSheafData.vanishingIdeal
      (⟨r.base '' (T : Set A), hImageClosed⟩ : TopologicalSpace.Closeds C)
    have hclosure :
        TopologicalSpace.Closeds.closure (r.base '' (T : Set A)) =
          ⟨r.base '' (T : Set A), hImageClosed⟩ :=
      TopologicalSpace.Closeds.ext hImageClosed.closure_eq
    have hmap : I.map r = J := by
      dsimp [J]
      rw [Scheme.IdealSheafData.map_vanishingIdeal]
      rw [hclosure]
    have hle : J ≤ I.map r := by rw [hmap]
    let k := I.subschemeMap J r hle
    have hkfac := I.subschemeMap_subschemeι J r hle
    have hkcomp : IsProper (k ≫ J.subschemeι) := by
      rw [hkfac]
      exact hR
    have hk : IsProper k := IsProper.of_comp k J.subschemeι
    have hJ : IsProper (J.subschemeι ≫ q) := hImage
    have hcomp : IsProper (k ≫ (J.subschemeι ≫ q)) := by
      infer_instance
    have hfac : k ≫ (J.subschemeι ≫ q) = I.subschemeι ≫ (r ≫ q) := by
      calc
        k ≫ (J.subschemeι ≫ q) = (k ≫ J.subschemeι) ≫ q := by
          rw [Category.assoc]
        _ = (I.subschemeι ≫ r) ≫ q := by rw [hkfac]
        _ = I.subschemeι ≫ (r ≫ q) := by rw [Category.assoc]
    have hresult : IsProper (I.subschemeι ≫ (r ≫ q)) := by
      rw [← hfac]
      exact hcomp
    show IsProper (I.subschemeι ≫ (r ≫ q))
    exact hresult

/-- A closed subset `T` of `C` is proper over `S` along `p` if and only if its preimage under an
isomorphism `e : A ≅ C` is proper over `S` along `e.hom ≫ p`. -/
theorem properOver_preimage_iso
    {A C S : Scheme.{u}} (e : A ≅ C) (p : C ⟶ S)
    [LocallyOfFiniteType p] (T : TopologicalSpace.Closeds C) :
    IsProperOver p T ↔
      IsProperOver (e.hom ≫ p)
        ⟨e.hom.base ⁻¹' (T : Set C), T.2.preimage (Scheme.Hom.continuous e.hom)⟩ := by
  classical
  have : LocallyOfFiniteType (e.hom ≫ p) := by infer_instance
  let T' : TopologicalSpace.Closeds A :=
    ⟨e.hom.base ⁻¹' (T : Set C), T.2.preimage (Scheme.Hom.continuous e.hom)⟩
  let I := Scheme.IdealSheafData.vanishingIdeal T
  let K := I.comap e.hom
  let J := Scheme.IdealSheafData.vanishingIdeal T'
  have : IsIso (pullback.snd e.hom I.subschemeι) := inferInstance
  have hsupport : K.support = T' := by
    ext x
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have hredI : IsReduced I.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal T
  let : IsReduced K.subscheme := by
    let : IsIso e.hom := inferInstance
    have hIso : K.subscheme ≅ I.subscheme :=
      I.comapIso e.hom ≪≫ asIso (pullback.snd e.hom I.subschemeι)
    exact ObjectProperty.prop_of_iso IsReduced hIso.symm hredI
  have hKJ : K = J :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme K T' hsupport
  let eK : K.subscheme ≅ I.subscheme := by
    let : IsIso e.hom := inferInstance
    exact I.comapIso e.hom ≪≫ asIso (pullback.snd e.hom I.subschemeι)
  have hdiag : eK.hom ≫ I.subschemeι = K.subschemeι ≫ e.hom := by
    dsimp [eK]
    rw [Scheme.IdealSheafData.comapIso_hom_snd]
    simp [K, Scheme.IdealSheafData.subschemeMap_subschemeι]
  constructor
  · intro hI
    show IsProper (J.subschemeι ≫ (e.hom ≫ p))
    rw [← hKJ]
    rw [← Category.assoc, ← hdiag]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)
      eK.hom (I.subschemeι ≫ p)).2 hI
  · intro hK
    change IsProper (J.subschemeι ≫ (e.hom ≫ p)) at hK
    rw [← hKJ] at hK
    change IsProper (K.subschemeι ≫ e.hom ≫ p) at hK
    rw [← Category.assoc, ← hdiag] at hK
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)
      eK.hom (I.subschemeι ≫ p)).1 (by simpa [Category.assoc] using hK)

/-- A monomorphism of sheaves of abelian groups is injective on sections over every object. -/
theorem mono_app_injective {C : Type u} [Category C]
    {J : GrothendieckTopology C} {F G : Sheaf J AddCommGrpCat.{v}}
    (i : F ⟶ G) [Mono i] (U : Cᵒᵖ) : Function.Injective (i.hom.app U) := by
  have hmono : Mono ((sheafToPresheaf J AddCommGrpCat).map i) :=
    Functor.map_mono (sheafToPresheaf J AddCommGrpCat) i
  have hmonoU :=
    (NatTrans.mono_iff_mono_app
      (f := (sheafToPresheaf J AddCommGrpCat).map i)).mp hmono U
  exact (AddCommGrpCat.mono_iff_injective _).mp hmonoU

/-- Given monomorphisms `i : F ⟶ H` and `j : G ⟶ H` of sheaves of abelian groups such that every
section of `H` in the image of `i` lies in the image of `j`, the morphism `m : F ⟶ G` with
`m ≫ j = i`. -/
noncomputable def factorOfRange {C : Type u} [Category C]
    {J : GrothendieckTopology C} {F G H : Sheaf J AddCommGrpCat.{v}}
    (i : F ⟶ H) (j : G ⟶ H) [Mono i] [Mono j]
    (h : ∀ U (x : H.obj.obj U), (∃ y, i.hom.app U y = x) →
      ∃ y, j.hom.app U y = x) : {m : F ⟶ G // m ≫ j = i} := by
  let app (U : Cᵒᵖ) : F.obj.obj U →+ G.obj.obj U := {
    toFun := fun x => Classical.choose (h U (i.hom.app U x) ⟨x, rfl⟩)
    map_zero' := by
      apply mono_app_injective j U
      change j.hom.app U
        (Classical.choose (h U (i.hom.app U 0) ⟨0, rfl⟩)) = j.hom.app U 0
      rw [Classical.choose_spec (h U (i.hom.app U 0) ⟨0, rfl⟩)]
      simp
    map_add' := by
      intro x y
      let hp : ∃ z, i.hom.app U z = i.hom.app U (x + y) := ⟨x + y, rfl⟩
      let hx : ∃ z, i.hom.app U z = i.hom.app U x := ⟨x, rfl⟩
      let hy : ∃ z, i.hom.app U z = i.hom.app U y := ⟨y, rfl⟩
      apply mono_app_injective j U
      change j.hom.app U (Classical.choose (h U (i.hom.app U (x + y)) hp)) =
        j.hom.app U (Classical.choose (h U (i.hom.app U x) hx) +
          Classical.choose (h U (i.hom.app U y) hy))
      calc
        j.hom.app U (Classical.choose (h U (i.hom.app U (x + y)) hp)) =
            i.hom.app U (x + y) := Classical.choose_spec (h U _ hp)
        _ = i.hom.app U x + i.hom.app U y := map_add _ _ _
        _ = j.hom.app U (Classical.choose (h U (i.hom.app U x) hx)) +
            j.hom.app U (Classical.choose (h U (i.hom.app U y) hy)) := by
              rw [Classical.choose_spec (h U _ hx), Classical.choose_spec (h U _ hy)]
        _ = j.hom.app U (Classical.choose (h U (i.hom.app U x) hx) +
            Classical.choose (h U (i.hom.app U y) hy)) := (map_add _ _ _).symm
  }
  let m : F ⟶ G := ⟨{
    app := fun U => AddCommGrpCat.ofHom (app U)
    naturality := by
      intro U V f
      ext x
      change (app V) ((F.obj.map f) x) = (G.obj.map f) ((app U) x)
      apply mono_app_injective j V
      let hFx : ∃ z, i.hom.app V z = i.hom.app V ((F.obj.map f) x) :=
        ⟨(F.obj.map f) x, rfl⟩
      let hx : ∃ z, i.hom.app U z = i.hom.app U x := ⟨x, rfl⟩
      change j.hom.app V (Classical.choose (h V (i.hom.app V ((F.obj.map f) x)) hFx)) =
        j.hom.app V ((G.obj.map f) (Classical.choose (h U (i.hom.app U x) hx)))
      calc
        _ = i.hom.app V ((F.obj.map f) x) := Classical.choose_spec (h V _ hFx)
        _ = (H.obj.map f) (i.hom.app U x) := by
          have hn := congrArg (fun k => ConcreteCategory.hom k) (i.hom.naturality f)
          simp
        _ = (H.obj.map f)
            (j.hom.app U (Classical.choose (h U (i.hom.app U x) hx))) := by
          rw [Classical.choose_spec (h U (i.hom.app U x) hx)]
        _ = j.hom.app V ((G.obj.map f)
            (Classical.choose (h U (i.hom.app U x) hx))) := by
          have hn := congrArg (fun k => ConcreteCategory.hom k) (j.hom.naturality f)
          simp
  }⟩
  refine ⟨m, ?_⟩
  ext U x
  change j.hom.app U (app U x) = i.hom.app U x
  dsimp [app]
  exact Classical.choose_spec (h U (i.hom.app U x) ⟨x, rfl⟩)

/-- Given monomorphisms `i : F ⟶ H` and `j : G ⟶ H` of sheaves of abelian groups with the same
image on sections over every object, the isomorphism `e : F ≅ G` with `e.hom ≫ j = i`. -/
noncomputable def isoOfRangeEq {C : Type u} [Category C]
    {J : GrothendieckTopology C} {F G H : Sheaf J AddCommGrpCat.{v}}
    (i : F ⟶ H) (j : G ⟶ H) [Mono i] [Mono j]
    (h : ∀ U (x : H.obj.obj U),
      (∃ y, i.hom.app U y = x) ↔ ∃ y, j.hom.app U y = x) :
    {e : F ≅ G // e.hom ≫ j = i} := by
  let m := factorOfRange i j (fun U x hx => (h U x).mp hx)
  let n := factorOfRange j i (fun U x hx => (h U x).mpr hx)
  have hm : m.val ≫ n.val = 𝟙 _ := by
    apply (cancel_mono i).1
    calc
      (m.val ≫ n.val) ≫ i = m.val ≫ (n.val ≫ i) := by cat_disch
      _ = m.val ≫ j := by rw [n.property]
      _ = i := m.property
  have hn : n.val ≫ m.val = 𝟙 _ := by
    apply (cancel_mono j).1
    calc
      (n.val ≫ m.val) ≫ j = n.val ≫ (m.val ≫ j) := by cat_disch
      _ = n.val ≫ i := by rw [m.property]
      _ = j := n.property
  refine ⟨⟨m.val, n.val, hm, hn⟩, ?_⟩
  change m.val ≫ j = i
  exact m.property

/-- An open subscheme `W` of the scheme underlying an object `U` of the small étale site of `S`,
as an object of that site via the composite `W ⟶ U ⟶ S`. -/
noncomputable def openEtaleObject (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS)
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens) : SmallEtale B S hS := by
  let Vbase : B.Scheme := ⟨(↑W : Scheme),
    lt_of_le_of_lt (Scheme.size_coe_opens_le _ W) U.obj.left.property⟩
  let fscheme : B.inclusion.obj Vbase ⟶ B.inclusion.obj U.obj.left := W.ι
  let fbase : Vbase ⟶ U.obj.left := B.inclusion.preimage fscheme
  let Vover : BigEtaleOver B S hS := Over.mk (fbase ≫ U.obj.hom)
  have hetale : Etale (B.inclusion.map (fbase ≫ U.obj.hom)) := by
    rw [Functor.map_comp, B.inclusion.map_preimage fscheme]
    infer_instance
  exact ⟨Vover, hetale⟩

/-- The morphism `openEtaleObject B S hS U W ⟶ U` of the small étale site given by the inclusion
of the open subscheme `W`. -/
noncomputable def openEtaleInclusion (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS)
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens) :
    openEtaleObject B S hS U W ⟶ U := by
  let Vbase := B.obj (↑W : Scheme)
    (lt_of_le_of_lt (Scheme.size_coe_opens_le _ W) U.obj.left.property)
  let fscheme : B.inclusion.obj Vbase ⟶ B.inclusion.obj U.obj.left := W.ι
  let fbase : Vbase ⟶ U.obj.left := B.inclusion.preimage fscheme
  exact ⟨Over.homMk fbase⟩

/-- The morphism of schemes underlying `openEtaleInclusion B S hS U W` is the open immersion
`W.ι`. -/
theorem openEtaleInclusion_map (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS)
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens) :
    (SmallEtale.toScheme B S hS).map (openEtaleInclusion B S hS U W) = W.ι := by
  let Vbase : B.Scheme := ⟨(↑W : Scheme),
    lt_of_le_of_lt (Scheme.size_coe_opens_le _ W) U.obj.left.property⟩
  let fscheme : B.inclusion.obj Vbase ⟶ B.inclusion.obj U.obj.left := W.ι
  let fbase : Vbase ⟶ U.obj.left := B.inclusion.preimage fscheme
  show B.inclusion.map fbase = fscheme
  exact B.inclusion.map_preimage fscheme

/-- For `a : A ⟶ X` and `b : X ⟶ S` with `a ≫ b = bA`, and `f : T ⟶ S`, the square formed by the
induced morphism `A ×_S T ⟶ X ×_S T`, the first projections and `a` is a pullback square. -/
theorem baseChange_square {C : Type*} [Category C]
    [CategoryTheory.Limits.HasPullbacks C]
    {A X S T : C} (a : A ⟶ X) (b : X ⟶ S) (bA : A ⟶ S) (f : T ⟶ S)
    (h : a ≫ b = bA) :
    IsPullback
      (pullback.lift (pullback.fst bA f ≫ a) (pullback.snd bA f)
        (by rw [Category.assoc, h]; exact pullback.condition))
      (pullback.fst bA f) (pullback.fst b f) a := by
  refine ⟨⟨by exact pullback.lift_fst _ _ _⟩,
    ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    refine pullback.lift c.snd (c.fst ≫ pullback.snd b f) ?_
    calc
      c.snd ≫ bA = c.snd ≫ a ≫ b := by rw [← h]
      _ = c.fst ≫ pullback.fst b f ≫ b := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ b) c.condition.symm
      _ = c.fst ≫ pullback.snd b f ≫ f := by rw [pullback.condition]
    all_goals simp only [Category.assoc]
  · intro c
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst] using
        c.condition.symm
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  · intro c
    exact pullback.lift_fst _ _ _
  · intro c m hm₁ hm₂
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using hm₂
    · simpa only [Category.assoc, pullback.lift_snd] using
        congrArg (fun k => k ≫ pullback.snd b f) hm₁

/-- For a morphism `j : V ⟶ U` of the small étale site of `S` and `f : T ⟶ S`, the base change of
`j` along `f` and `j` itself, together with the first projections `V ×_S T ⟶ V` and
`U ×_S T ⟶ U`, form a pullback square of schemes. -/
theorem smallEtaleBaseChange_isPullback
    (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)
    (U V : SmallEtale B S.obj S.property) (j : V ⟶ U) :
    IsPullback
      (B.inclusion.map ((Over.pullback f).map
        ((SmallEtale.inclusion B S.obj S.property).map j)).left)
      (B.inclusion.map (CategoryTheory.Limits.pullback.fst V.obj.hom f))
      (B.inclusion.map (CategoryTheory.Limits.pullback.fst U.obj.hom f))
      (B.inclusion.map ((SmallEtale.inclusion B S.obj S.property).map j).left) := by
  let := hasPullbacks_bigEtaleSite B
  let := preservesPullbacks_bigEtaleSiteInclusion B
  let jOver := (SmallEtale.inclusion B S.obj S.property).map j
  let k := (Over.pullback f).map jOver
  have hpb : IsPullback k.left (CategoryTheory.Limits.pullback.fst V.obj.hom f)
      (CategoryTheory.Limits.pullback.fst U.obj.hom f) jOver.left := by
    show IsPullback
      (CategoryTheory.Limits.pullback.lift
        (CategoryTheory.Limits.pullback.fst V.obj.hom f ≫ jOver.left)
        (CategoryTheory.Limits.pullback.snd V.obj.hom f) ?_)
      (CategoryTheory.Limits.pullback.fst V.obj.hom f)
      (CategoryTheory.Limits.pullback.fst U.obj.hom f) jOver.left
    exact baseChange_square jOver.left U.obj.hom V.obj.hom f (Over.w jOver)
  exact hpb.map B.inclusion

/-- The base change along `f` of a morphism of the small étale site whose underlying morphism of
schemes is an open immersion again has an open immersion as underlying morphism of schemes. -/
theorem smallEtaleBaseChange_isOpenImmersion
    (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)
    (U V : SmallEtale B S.obj S.property) (j : V ⟶ U)
    [IsOpenImmersion ((SmallEtale.toScheme B S.obj S.property).map j)] :
    IsOpenImmersion ((SmallEtale.toScheme B T.1 T.property).map
      ((smallEtaleBaseChange B f).map j)) := by
  let := hasPullbacks_bigEtaleSite B
  let := preservesPullbacks_bigEtaleSiteInclusion B
  have hpb := smallEtaleBaseChange_isPullback B f U V j
  show IsOpenImmersion
    (B.inclusion.map ((Over.pullback f).map
      ((SmallEtale.inclusion B S.obj S.property).map j)).left)
  exact MorphismProperty.of_isPullback hpb.flip
    (show IsOpenImmersion
      (B.inclusion.map ((SmallEtale.inclusion B S.obj S.property).map j).left) from
      ‹IsOpenImmersion ((SmallEtale.toScheme B S.obj S.property).map j)›)

/-- For a morphism `j : V ⟶ U` of the small étale site of `S` whose underlying morphism is an open
immersion, the range of its base change along `f : T ⟶ S` is the preimage of the range of `j`
under the projection `U ×_S T ⟶ U`. -/
theorem smallEtaleBaseChange_openRange
    (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)
    (U V : SmallEtale B S.obj S.property) (j : V ⟶ U)
    [IsOpenImmersion ((SmallEtale.toScheme B S.obj S.property).map j)]
    [IsOpenImmersion ((SmallEtale.toScheme B T.1 T.property).map
      ((smallEtaleBaseChange B f).map j))] :
    ((SmallEtale.toScheme B T.1 T.property).map
      ((smallEtaleBaseChange B f).map j)).opensRange =
      B.inclusion.map (CategoryTheory.Limits.pullback.fst U.obj.hom f) ⁻¹ᵁ
        ((SmallEtale.toScheme B S.obj S.property).map j).opensRange := by
  let := hasPullbacks_bigEtaleSite B
  let := preservesPullbacks_bigEtaleSiteInclusion B
  have hpb := smallEtaleBaseChange_isPullback B f U V j
  let q := B.inclusion.map (CategoryTheory.Limits.pullback.fst U.obj.hom f)
  let jScheme := B.inclusion.map ((SmallEtale.inclusion B S.obj S.property).map j).left
  let kScheme := B.inclusion.map ((Over.pullback f).map
    ((SmallEtale.inclusion B S.obj S.property).map j)).left
  have : IsOpenImmersion jScheme :=
    ‹IsOpenImmersion ((SmallEtale.toScheme B S.obj S.property).map j)›
  have htop : IsOpenImmersion (CategoryTheory.Limits.pullback.fst q jScheme) := by
    infer_instance
  have hk : IsOpenImmersion kScheme := by
    show IsOpenImmersion
      (B.inclusion.map ((Over.pullback f).map
        ((SmallEtale.inclusion B S.obj S.property).map j)).left)
    rw [← hpb.isoPullback_hom_fst]
    infer_instance
  let := hk
  show (B.inclusion.map ((Over.pullback f).map
      ((SmallEtale.inclusion B S.obj S.property).map j)).left).opensRange =
    q ⁻¹ᵁ jScheme.opensRange
  have hcomp : hpb.isoPullback.hom ≫
      CategoryTheory.Limits.pullback.fst q jScheme =
        B.inclusion.map ((Over.pullback f).map
          ((SmallEtale.inclusion B S.obj S.property).map j)).left := by
    simp [q, jScheme]
  have hcompOpen : IsOpenImmersion
      (hpb.isoPullback.hom ≫ CategoryTheory.Limits.pullback.fst q jScheme) := by
    infer_instance
  have hrangeEq :
      (B.inclusion.map ((Over.pullback f).map
        ((SmallEtale.inclusion B S.obj S.property).map j)).left).opensRange =
      (hpb.isoPullback.hom ≫ CategoryTheory.Limits.pullback.fst q jScheme).opensRange := by
    have heq :
        (⟨hpb.isoPullback.hom ≫ CategoryTheory.Limits.pullback.fst q jScheme,
          hcompOpen⟩ : {k : Scheme.Hom _ _ // IsOpenImmersion k}) =
        ⟨B.inclusion.map ((Over.pullback f).map
          ((SmallEtale.inclusion B S.obj S.property).map j)).left, hk⟩ :=
      Subtype.ext hcomp
    exact (congrArg
      (fun (k : {k : Scheme.Hom _ _ // IsOpenImmersion k}) =>
        let : IsOpenImmersion k.val := k.property
        Scheme.Hom.opensRange k.val) heq).symm
  calc
    _ = (hpb.isoPullback.hom ≫
        CategoryTheory.Limits.pullback.fst q jScheme).opensRange := hrangeEq
    _ = (CategoryTheory.Limits.pullback.fst q jScheme).opensRange :=
      Scheme.Hom.opensRange_comp_of_isIso _ _
    _ = q ⁻¹ᵁ jScheme.opensRange :=
      Scheme.Hom.opensRange_pullbackFst _ _

/-- The range of the morphism of schemes underlying `openEtaleInclusion B S hS U W` is `W`. -/
private theorem range_map_openEtaleInclusion (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS)
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens) :
    Set.range ((SmallEtale.toScheme B S hS).map (openEtaleInclusion B S hS U W)).base = W := by
  rw [openEtaleInclusion_map]
  exact Scheme.Opens.range_ι W

/-- Restricting a section along the inclusion of an open `W` kills it iff `W` is in its zero
locus. -/
private theorem map_openEtaleInclusion_eq_zero_iff (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U : SmallEtale B S hS) (s : F.obj.obj (Opposite.op U))
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens) :
    F.obj.map (openEtaleInclusion B S hS U W).op s = 0 ↔
      W ≤ SmallEtale.zeroOpen B S hS F U s := by
  rw [SmallEtale.map_eq_zero_iff_range_subset_zeroOpen, range_map_openEtaleInclusion]
  rfl

/-- The support of a section is unchanged by applying a monomorphism of sheaves of abelian groups
on the small étale site. -/
theorem supportSection_eq_of_mono (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {F G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v}}
    (φ : F ⟶ G) [Mono φ] (U : SmallEtale B S hS)
    (s : F.obj.obj (Opposite.op U)) :
    SmallEtale.supportSection B S hS G U
      (φ.hom.app (Opposite.op U) s) =
    SmallEtale.supportSection B S hS F U s := by
  have h (W : ((SmallEtale.toScheme B S hS).obj U).Opens) :
      W ≤ SmallEtale.zeroOpen B S hS G U (φ.hom.app (Opposite.op U) s) ↔
        W ≤ SmallEtale.zeroOpen B S hS F U s := by
    rw [← map_openEtaleInclusion_eq_zero_iff, ← map_openEtaleInclusion_eq_zero_iff]
    have hnat : G.obj.map (openEtaleInclusion B S hS U W).op (φ.hom.app (Opposite.op U) s) =
        φ.hom.app _ (F.obj.map (openEtaleInclusion B S hS U W).op s) := by simp
    rw [hnat]
    exact map_eq_zero_iff _ (mono_app_injective φ _)
  have key := le_antisymm ((h _).2 le_rfl) ((h _).1 le_rfl)
  simp only [SmallEtale.supportSection, key]

/-- The range of the open immersion underlying `openEtaleInclusion B S hS U W` is `W`. -/
theorem openEtaleInclusion_openRange (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS)
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens)
    [IsOpenImmersion ((SmallEtale.toScheme B S hS).map
      (openEtaleInclusion B S hS U W))] :
    ((SmallEtale.toScheme B S hS).map (openEtaleInclusion B S hS U W)).opensRange = W := by
  let i := openEtaleInclusion B S hS U W
  have hmap := openEtaleInclusion_map B S hS U W
  have hW : IsOpenImmersion W.ι := by
    rw [Scheme.Opens.ι]
    exact IsOpenImmersion.ofRestrict _ _
  have heq :
      (⟨(SmallEtale.toScheme B S hS).map i,
        ‹IsOpenImmersion ((SmallEtale.toScheme B S hS).map i)›⟩ :
        {k : Scheme.Hom _ _ // IsOpenImmersion k}) = ⟨W.ι, hW⟩ :=
    Subtype.ext hmap
  calc
    ((SmallEtale.toScheme B S hS).map i).opensRange = W.ι.opensRange := by
      have h := congrArg (fun k : {k : Scheme.Hom _ _ // IsOpenImmersion k} =>
        let : IsOpenImmersion k.val := k.property
        Scheme.Hom.opensRange k.val) heq
      exact h
    _ = W := Scheme.Opens.opensRange_ι W

/-- The range of the base change along `f : X ⟶ Y` of the inclusion of an open subscheme `W` of
`V` is the preimage of `W` under the projection `V ×_Y X ⟶ V`. -/
theorem smallEtaleBaseChange_openEtaleInclusion_opens
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    (V : SmallEtale B Y.obj Y.property)
    (W : ((SmallEtale.toScheme B Y.obj Y.property).obj V).Opens)
    [IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map
        (openEtaleInclusion B Y.obj Y.property V W)))] :
    ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map (openEtaleInclusion B Y.obj Y.property V W))).opensRange =
      B.inclusion.map (CategoryTheory.Limits.pullback.fst V.obj.hom f) ⁻¹ᵁ W := by
  let i := openEtaleInclusion B Y.obj Y.property V W
  have : IsOpenImmersion ((SmallEtale.toScheme B Y.obj Y.property).map i) := by
    rw [openEtaleInclusion_map]
    rw [Scheme.Opens.ι]
    exact IsOpenImmersion.ofRestrict _ _
  have : IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map i)) :=
    smallEtaleBaseChange_isOpenImmersion B f V (openEtaleObject B Y.obj Y.property V W) i
  rw [smallEtaleBaseChange_openRange B f V (openEtaleObject B Y.obj Y.property V W) i,
    openEtaleInclusion_openRange]

/-- For a section `s` of `F` over `V ×_Y X` whose support is proper over `V`, the support of `s`
regarded as a section of the direct image of `F` along `f` over `V` is the image of its support
under the projection `V ×_Y X ⟶ V`. -/
theorem supportSection_smallEtalePushforward_eq_image
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property)
    (s : F.obj.obj (Opposite.op ((smallEtaleBaseChange B f).obj V)))
    (hproper : SmallEtale.properSupportSections B f F V s) :
    SmallEtale.supportSection B Y.obj Y.property
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{v}
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B X.obj X.property)).obj F) V s =
      (B.inclusion.map (CategoryTheory.Limits.pullback.fst V.obj.hom f)).base ''
        SmallEtale.supportSection B X.obj X.property F
          ((smallEtaleBaseChange B f).obj V) s := by
  classical
  let := hasPullbacks_bigEtaleSite B
  let := preservesPullbacks_bigEtaleSiteInclusion B
  let P := B.inclusion.map (CategoryTheory.Limits.pullback.fst V.obj.hom f)
  have : LocallyOfFiniteType P :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback V.obj.hom f).map B.inclusion).flip
      ‹LocallyOfFiniteType (B.inclusion.map f)›
  let Xv := (SmallEtale.toScheme B X.obj X.property).obj ((smallEtaleBaseChange B f).obj V)
  let Yv := (SmallEtale.toScheme B Y.obj Y.property).obj V
  let sx := SmallEtale.supportSection B X.obj X.property F
    ((smallEtaleBaseChange B f).obj V) s
  let T : TopologicalSpace.Closeds Xv :=
    ⟨sx, (SmallEtale.zeroOpen B X.obj X.property F
      ((smallEtaleBaseChange B f).obj V) s).isOpen.isClosed_compl⟩
  have hproper' : IsProperOver P T := by
    show IsProper ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ P)
    exact hproper
  have hclosed : IsClosed (P.base '' (T : Set Xv)) := by
    exact isClosed_image_of_isProperOver P (𝟙 Yv) P
      (by simp) T hproper'
  let t := ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)).obj F
  have hkey (W : Yv.Opens) : W ≤ SmallEtale.zeroOpen B Y.obj Y.property t V s ↔
      P ⁻¹ᵁ W ≤ SmallEtale.zeroOpen B X.obj X.property F ((smallEtaleBaseChange B f).obj V) s := by
    let i := openEtaleInclusion B Y.obj Y.property V W
    have : IsOpenImmersion ((SmallEtale.toScheme B Y.obj Y.property).map i) := by
      rw [openEtaleInclusion_map, Scheme.Opens.ι]
      exact IsOpenImmersion.ofRestrict _ _
    have : IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map
        ((smallEtaleBaseChange B f).map i)) :=
      smallEtaleBaseChange_isOpenImmersion B f V _ i
    rw [← map_openEtaleInclusion_eq_zero_iff B Y.obj Y.property t V s W]
    change F.obj.map ((smallEtaleBaseChange B f).map i).op s = 0 ↔ _
    rw [SmallEtale.map_eq_zero_iff_le_zeroOpen, smallEtaleBaseChange_openEtaleInclusion_opens]
    rfl
  ext y
  constructor
  · intro hy
    by_contra hyImage
    have hW : (⟨(P.base '' (T : Set Xv))ᶜ, hclosed.isOpen_compl⟩ : Yv.Opens) ≤
        SmallEtale.zeroOpen B Y.obj Y.property t V s :=
      (hkey _).2 fun x hx => by_contra fun hxZ => hx ⟨x, hxZ, rfl⟩
    exact hy (hW hyImage)
  · rintro ⟨x, hx, rfl⟩ hzero
    exact hx ((hkey _).1 le_rfl hzero)

/-- The support of the restriction of a section `s` along an isomorphism `a : V ⟶ U` of the small
étale site is the preimage of the support of `s` under the underlying morphism of schemes. -/
theorem supportSection_map_iso (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    {U V : SmallEtale B S hS} (a : V ⟶ U) [IsIso a]
    (s : F.obj.obj (Opposite.op U)) :
    SmallEtale.supportSection B S hS F V
      (F.obj.map a.op s) =
      ((SmallEtale.toScheme B S hS).map a).base ⁻¹'
        SmallEtale.supportSection B S hS F U s := by
  let aScheme := (SmallEtale.toScheme B S hS).map a
  have hkey (W : ((SmallEtale.toScheme B S hS).obj V).Opens) :
      W ≤ SmallEtale.zeroOpen B S hS F V (F.obj.map a.op s) ↔
        aScheme.base '' W ⊆ SmallEtale.zeroOpen B S hS F U s := by
    rw [← map_openEtaleInclusion_eq_zero_iff]
    have : F.obj.map (openEtaleInclusion B S hS V W ≫ a).op s =
        F.obj.map (openEtaleInclusion B S hS V W).op (F.obj.map a.op s) := by simp
    rw [← this, SmallEtale.map_eq_zero_iff_range_subset_zeroOpen, Functor.map_comp,
      Scheme.Hom.comp_base]
    change Set.range (aScheme.base ∘ _) ⊆ _ ↔ _
    rw [Set.range_comp, ← range_map_openEtaleInclusion B S hS V W]
    rfl
  have hzero : SmallEtale.zeroOpen B S hS F V (F.obj.map a.op s) = aScheme ⁻¹ᵁ
      SmallEtale.zeroOpen B S hS F U s :=
    le_antisymm (fun x hx => (hkey _).1 le_rfl ⟨x, hx, rfl⟩)
      ((hkey _).2 (Set.image_subset_iff.2 subset_rfl))
  ext x
  change x ∉ (SmallEtale.zeroOpen B S hS F V (F.obj.map a.op s) : Set _) ↔
    aScheme x ∉ (SmallEtale.zeroOpen B S hS F U s : Set _)
  rw [hzero]
  rfl

/-- Proper-support direct image as a functor on abelian étale sheaves. -/
public noncomputable def properSupportFunctor
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)] :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v} ⥤
      Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{v} where
  obj F := (SmallEtale.fShriekSubsheaf B f F).val.obj.left
  map φ := (SmallEtale.fShriekMap B f _ _ φ).val
  map_id F := SmallEtale.fShriekMap_id B f F
  map_comp φ ψ :=
    SmallEtale.fShriekMap_comp B f _ _ _ φ ψ

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme}
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [LocallyOfFiniteType (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})

/-- The canonical identification of iterated proper-support direct image with
proper-support direct image along the composite, as subsheaves of the direct
image along the composite. -/
@[sga "4 XVII 6.1.3" "partial"]
public noncomputable def properSupportSheaf_compIso
    [IsSeparated (B.inclusion.map f)] [IsSeparated (B.inclusion.map g)] :
    letI : LocallyOfFiniteType (B.inclusion.map (f ≫ g)) :=
      by rw [Functor.map_comp]; infer_instance
    let gStar := (smallEtaleBaseChange B g).sheafPushforwardContinuous
      AddCommGrpCat.{v} (SmallEtale.topology B Z.obj Z.property)
        (SmallEtale.topology B Y.obj Y.property)
    let fBang := (SmallEtale.fShriekSubsheaf B f F).val
    let gBang := (SmallEtale.fShriekSubsheaf B g fBang.obj.left).val
    let fgBang := (SmallEtale.fShriekSubsheaf B (f ≫ g) F).val
    let directImageCompIso := Functor.sheafPushforwardContinuousComp'
      (smallEtaleBaseChange_compIso B X Y Z f g).val
      AddCommGrpCat.{v} (SmallEtale.topology B Z.obj Z.property)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)
    { e : gBang.obj.left ≅ fgBang.obj.left //
      e.hom ≫ fgBang.arrow =
        gBang.arrow ≫ gStar.map fBang.arrow ≫
          (directImageCompIso.app F).hom } := by
  classical
  letI : LocallyOfFiniteType (B.inclusion.map (f ≫ g)) := by
    rw [Functor.map_comp]
    infer_instance
  let gStar := (smallEtaleBaseChange B g).sheafPushforwardContinuous
    AddCommGrpCat.{v} (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B Y.obj Y.property)
  let fStar := (smallEtaleBaseChange B f).sheafPushforwardContinuous
    AddCommGrpCat.{v} (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)
  let fBang := (SmallEtale.fShriekSubsheaf B f F).val
  let gBang := (SmallEtale.fShriekSubsheaf B g fBang.obj.left).val
  let fgBang := (SmallEtale.fShriekSubsheaf B (f ≫ g) F).val
  let d := Functor.sheafPushforwardContinuousComp'
    (smallEtaleBaseChange_compIso B X Y Z f g).val
    AddCommGrpCat.{v} (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)
  let fgStar := (smallEtaleBaseChange B (f ≫ g)).sheafPushforwardContinuous
    AddCommGrpCat.{v} (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B X.obj X.property)
  let i := gBang.arrow ≫ gStar.map fBang.arrow ≫ (d.app F).hom
  let j := fgBang.arrow
  have hmonoPresheaf : Mono ((sheafToPresheaf
      (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{v}).map
        (gStar.map fBang.arrow)) := by
    apply (NatTrans.mono_iff_mono_app _).2
    intro V
    apply (AddCommGrpCat.mono_iff_injective _).2
    intro x y hxy
    change fBang.arrow.hom.app (Opposite.op ((smallEtaleBaseChange B g).obj V.unop)) x =
      fBang.arrow.hom.app (Opposite.op ((smallEtaleBaseChange B g).obj V.unop)) y at hxy
    have hmonoApp : Mono (fBang.arrow.hom.app
        (Opposite.op ((smallEtaleBaseChange B g).obj V.unop))) :=
      (NatTrans.mono_iff_mono_app _).1
        (Functor.map_mono (sheafToPresheaf
          (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{v}) fBang.arrow)
        (Opposite.op ((smallEtaleBaseChange B g).obj V.unop))
    exact ((AddCommGrpCat.mono_iff_injective _).1 hmonoApp) hxy
  haveI : Mono (gStar.map fBang.arrow) :=
    Functor.mono_of_mono_map
      (sheafToPresheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{v})
      hmonoPresheaf
  haveI : Mono (d.app F).hom := by infer_instance
  haveI : Mono (gBang.arrow ≫ gStar.map fBang.arrow) := by infer_instance
  haveI : Mono i := by dsimp [i]; infer_instance
  haveI : Mono j := by dsimp [j]; infer_instance
  have hrange : ∀ (U : (SmallEtale B Z.obj Z.property)ᵒᵖ)
      (x : (fgStar.obj F).obj.obj U),
      (∃ y, i.hom.app U y = x) ↔ ∃ y, j.hom.app U y = x := by
    intro U x
    let V : SmallEtale B Z.obj Z.property := U.unop
    let VY := (smallEtaleBaseChange B g).obj V
    let VX := (smallEtaleBaseChange B f).obj VY
    let VComp := (smallEtaleBaseChange B (f ≫ g)).obj V
    let a := (smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app V
    let sx := F.obj.map a.op x
    let fSub := SmallEtale.fShriekSubsheaf B f F
    let gSub := SmallEtale.fShriekSubsheaf B g fBang.obj.left
    have hxd : (d.app F).hom.hom.app U sx = x := by
      let eSite := (smallEtaleBaseChange_compIso B X Y Z f g).val
      change F.obj.map (eSite.inv.app V).op (F.obj.map a.op x) = x
      let xComp : F.obj.obj (Opposite.op VComp) := x
      have ha' : eSite.inv.app V ≫ a = 𝟙 VComp := by
        dsimp [a, eSite]
        exact (smallEtaleBaseChange_compIso B X Y Z f g).val.inv_hom_id_app V
      have hmap := F.obj.map_comp a.op (eSite.inv.app V).op
      change F.obj.map (eSite.inv.app V).op (F.obj.map a.op xComp) = xComp
      change (F.obj.map a.op ≫ F.obj.map (eSite.inv.app V).op) xComp = xComp
      rw [hmap.symm, ← op_comp, ha']
      rw [op_id]
      simp
    have hri : (∃ y, i.hom.app U y = x) ↔
        ∃ t : fBang.obj.left.obj.obj (Opposite.op VY),
          fBang.arrow.hom.app (Opposite.op VY) t = sx ∧
            SmallEtale.properSupportSections B g fBang.obj.left V t := by
      constructor
      · rintro ⟨y, hy⟩
        let t := gBang.arrow.hom.app U y
        have hseq : (gStar.map fBang.arrow).hom.app U t = sx := by
          have hy0 : (d.app F).hom.hom.app U
              ((gStar.map fBang.arrow).hom.app U (gBang.arrow.hom.app U y)) = x := by
            exact hy
          apply mono_app_injective (d.app F).hom U
          exact hy0.trans hxd.symm
        change fBang.arrow.hom.app (Opposite.op VY) t = sx at hseq
        exact ⟨t, hseq, (gSub.property V t).mp ⟨y, rfl⟩⟩
      · rintro ⟨t, hsection, hproper⟩
        obtain ⟨y, hy⟩ := (gSub.property V t).mpr hproper
        refine ⟨y, ?_⟩
        have hseq : (gStar.map fBang.arrow).hom.app U
            (gBang.arrow.hom.app U y) = sx := by
          change fBang.arrow.hom.app (Opposite.op VY)
            (gBang.arrow.hom.app U y) = sx
          rw [hy, hsection]
        change (d.app F).hom.hom.app U
          ((gStar.map fBang.arrow).hom.app U (gBang.arrow.hom.app U y)) = x
        rw [hseq, hxd]
    have hcompSupport :
        (∃ t : fBang.obj.left.obj.obj (Opposite.op VY),
          fBang.arrow.hom.app (Opposite.op VY) t = sx ∧
            SmallEtale.properSupportSections B g fBang.obj.left V t) ↔
          SmallEtale.properSupportSections B (f ≫ g) F V x := by
      classical
      let := hasPullbacks_bigEtaleSite B
      let := preservesPullbacks_bigEtaleSiteInclusion B
      let P : (SmallEtale.toScheme B X.obj X.property).obj VX ⟶
          (SmallEtale.toScheme B Y.obj Y.property).obj VY :=
        B.inclusion.map (CategoryTheory.Limits.pullback.fst VY.obj.hom f)
      let Q : (SmallEtale.toScheme B Y.obj Y.property).obj VY ⟶
          (SmallEtale.toScheme B Z.obj Z.property).obj V :=
        B.inclusion.map (CategoryTheory.Limits.pullback.fst V.obj.hom g)
      let R : (SmallEtale.toScheme B X.obj X.property).obj VComp ⟶
          (SmallEtale.toScheme B Z.obj Z.property).obj V :=
        B.inclusion.map (CategoryTheory.Limits.pullback.fst V.obj.hom (f ≫ g))
      let aScheme := (SmallEtale.toScheme B X.obj X.property).map a
      have hVXscheme : (SmallEtale.toScheme B X.obj X.property).obj VX =
          B.inclusion.obj (CategoryTheory.Limits.pullback VY.obj.hom f) := by rfl
      have hVYscheme : (SmallEtale.toScheme B Y.obj Y.property).obj VY =
          B.inclusion.obj (CategoryTheory.Limits.pullback V.obj.hom g) := by rfl
      have : IsIso a := by dsimp [a]; infer_instance
      have : IsIso aScheme := Functor.map_isIso _ a
      let Tseq : TopologicalSpace.Closeds
          ((SmallEtale.toScheme B X.obj X.property).obj VX) :=
        ⟨SmallEtale.supportSection B X.obj X.property F VX sx,
          (SmallEtale.zeroOpen B X.obj X.property F VX sx).isOpen.isClosed_compl⟩
      let Tcomp : TopologicalSpace.Closeds
          ((SmallEtale.toScheme B X.obj X.property).obj VComp) :=
        ⟨SmallEtale.supportSection B X.obj X.property F VComp x,
          (SmallEtale.zeroOpen B X.obj X.property F VComp x).isOpen.isClosed_compl⟩
      have hsupportIso := supportSection_map_iso B X.obj X.property F a x
      have hTset :
          (Tseq : Set ((SmallEtale.toScheme B X.obj X.property).obj VX)) =
            aScheme.base ⁻¹'
              (Tcomp : Set ((SmallEtale.toScheme B X.obj X.property).obj VComp)) := by
        change SmallEtale.supportSection B X.obj X.property F VX sx =
          aScheme.base ⁻¹' SmallEtale.supportSection
            B X.obj X.property F VComp x
        exact hsupportIso
      let Tpre : TopologicalSpace.Closeds ((SmallEtale.toScheme B X.obj X.property).obj VX) :=
        ⟨aScheme.base ⁻¹' (Tcomp : Set _), Tcomp.2.preimage (Scheme.Hom.continuous aScheme)⟩
      have hTseq : Tseq = Tpre := TopologicalSpace.Closeds.ext hTset
      have hpbQ : IsPullback
          (B.inclusion.map (CategoryTheory.Limits.pullback.fst V.obj.hom g))
          (B.inclusion.map (CategoryTheory.Limits.pullback.snd V.obj.hom g))
          (B.inclusion.map V.obj.hom) (B.inclusion.map g) :=
        (IsPullback.of_hasPullback V.obj.hom g).map B.inclusion
      have hLFTQ : LocallyOfFiniteType Q :=
        MorphismProperty.of_isPullback hpbQ.flip ‹LocallyOfFiniteType (B.inclusion.map g)›
      let : LocallyOfFiniteType Q := hLFTQ
      have hSeparatedQ : IsSeparated Q :=
        MorphismProperty.of_isPullback hpbQ.flip ‹IsSeparated (B.inclusion.map g)›
      let : IsSeparated Q := hSeparatedQ
      have hpbP : IsPullback
          (B.inclusion.map (CategoryTheory.Limits.pullback.fst VY.obj.hom f))
          (B.inclusion.map (CategoryTheory.Limits.pullback.snd VY.obj.hom f))
          (B.inclusion.map VY.obj.hom) (B.inclusion.map f) :=
        (IsPullback.of_hasPullback VY.obj.hom f).map B.inclusion
      have hLFTP : LocallyOfFiniteType P :=
        MorphismProperty.of_isPullback hpbP.flip ‹LocallyOfFiniteType (B.inclusion.map f)›
      let : LocallyOfFiniteType P := hLFTP
      have hpbR : IsPullback
          (B.inclusion.map (CategoryTheory.Limits.pullback.fst V.obj.hom (f ≫ g)))
          (B.inclusion.map (CategoryTheory.Limits.pullback.snd V.obj.hom (f ≫ g)))
          (B.inclusion.map V.obj.hom) (B.inclusion.map (f ≫ g)) :=
        (IsPullback.of_hasPullback V.obj.hom (f ≫ g)).map B.inclusion
      have hLFTcomp : LocallyOfFiniteType (B.inclusion.map (f ≫ g)) := by
        rw [Functor.map_comp]
        infer_instance
      have hLFTR : LocallyOfFiniteType R :=
        MorphismProperty.of_isPullback hpbR.flip hLFTcomp
      let : LocallyOfFiniteType R := hLFTR
      have hLFTPQ : LocallyOfFiniteType (P ≫ Q) := by infer_instance
      let : LocallyOfFiniteType (P ≫ Q) := hLFTPQ
      have hproperCompSeq := @properOver_comp_iff_image _ _ _ P Q hLFTP hLFTQ
        hSeparatedQ Tseq
      have hproperTransport := @properOver_preimage_iso _ _ _ (asIso aScheme) R hLFTR Tcomp
      have ha : aScheme = B.inclusion.map
          ((Over.pullbackComp f g).inv.app V.obj).left := by
        have hsite := smallEtaleBaseChange_compIso_app B X Y Z f g V
        change B.inclusion.map ((SmallEtale.inclusion B X.obj X.property).map a).left =
          B.inclusion.map ((Over.pullbackComp f g).inv.app V.obj).left
        rw [hsite]
        rfl
      have hproj0 :
          ((Over.pullbackComp f g).inv.app V.obj).left ≫
              CategoryTheory.Limits.pullback.fst V.obj.hom (f ≫ g) =
              CategoryTheory.Limits.pullback.fst VY.obj.hom f ≫
              CategoryTheory.Limits.pullback.fst V.obj.hom g := by
        have hcomp :
            ((Over.pullbackComp f g).hom.app V.obj).left ≫
                CategoryTheory.Limits.pullback.fst
                  (CategoryTheory.Limits.pullback.snd V.obj.hom g) f ≫
                CategoryTheory.Limits.pullback.fst V.obj.hom g =
              CategoryTheory.Limits.pullback.fst V.obj.hom (f ≫ g) := by
          simp [Over.pullbackComp, Over.pullback, Category.assoc,
            CategoryTheory.Limits.pullback.lift_fst,
            CategoryTheory.Limits.pullback.lift_fst_assoc,
            Category.id_comp, Category.comp_id]
        rw [← hcomp, ← Category.assoc, ← Over.comp_left]
        simp [smallEtaleBaseChange_obj_obj,
          Over.pullback, VY]
      have hproj : aScheme ≫ R = P ≫ Q := by
        rw [ha]
        change B.inclusion.map ((Over.pullbackComp f g).inv.app V.obj).left ≫
            B.inclusion.map (CategoryTheory.Limits.pullback.fst V.obj.hom (f ≫ g)) =
          B.inclusion.map (CategoryTheory.Limits.pullback.fst VY.obj.hom f) ≫
            B.inclusion.map (CategoryTheory.Limits.pullback.fst V.obj.hom g)
        rw [← Functor.map_comp]
        rw [hproj0]
        rfl
      have htransportSeq : IsProperOver R Tcomp ↔
          IsProperOver (P ≫ Q) Tseq := by
        have hproperTransport' :
            IsProper ((Scheme.IdealSheafData.vanishingIdeal Tcomp).subschemeι ≫ R) ↔
              IsProper ((Scheme.IdealSheafData.vanishingIdeal Tpre).subschemeι ≫
                (aScheme ≫ R)) := by
          change IsProper ((Scheme.IdealSheafData.vanishingIdeal Tcomp).subschemeι ≫ R) ↔
            IsProper ((Scheme.IdealSheafData.vanishingIdeal Tpre).subschemeι ≫
              ((asIso aScheme).hom ≫ R))
          simpa only [show (asIso aScheme).hom = aScheme from rfl] using hproperTransport
        have hproperMove :
            IsProper ((Scheme.IdealSheafData.vanishingIdeal Tpre).subschemeι ≫
                (aScheme ≫ R)) ↔
              IsProper ((Scheme.IdealSheafData.vanishingIdeal Tseq).subschemeι ≫
                (P ≫ Q)) := by
          have hTtransport :
              IsProper ((Scheme.IdealSheafData.vanishingIdeal Tpre).subschemeι ≫
                  (aScheme ≫ R)) ↔
                IsProper ((Scheme.IdealSheafData.vanishingIdeal Tseq).subschemeι ≫
                  (aScheme ≫ R)) := by
            exact Iff.of_eq (congrArg
              (fun T : TopologicalSpace.Closeds
                  ((SmallEtale.toScheme B X.obj X.property).obj VX) =>
                IsProper ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫
                  (aScheme ≫ R))) hTseq.symm)
          have hmorph :
              (Scheme.IdealSheafData.vanishingIdeal Tseq).subschemeι ≫
                  (aScheme ≫ R) =
                (Scheme.IdealSheafData.vanishingIdeal Tseq).subschemeι ≫
                  (P ≫ Q) := by
            calc
              _ = ((Scheme.IdealSheafData.vanishingIdeal Tseq).subschemeι ≫ aScheme) ≫ R :=
                by rw [Category.assoc]
              _ = (Scheme.IdealSheafData.vanishingIdeal Tseq).subschemeι ≫
                    (aScheme ≫ R) := by rw [Category.assoc]
              _ = (Scheme.IdealSheafData.vanishingIdeal Tseq).subschemeι ≫ (P ≫ Q) := by
                    rw [hproj]
          have hArrow :
              IsProper ((Scheme.IdealSheafData.vanishingIdeal Tseq).subschemeι ≫
                  (aScheme ≫ R)) ↔
                IsProper ((Scheme.IdealSheafData.vanishingIdeal Tseq).subschemeι ≫
                  (P ≫ Q)) := Iff.of_eq (congrArg IsProper hmorph)
          exact hTtransport.trans hArrow
        change IsProper ((Scheme.IdealSheafData.vanishingIdeal Tcomp).subschemeι ≫ R) ↔
          IsProper ((Scheme.IdealSheafData.vanishingIdeal Tseq).subschemeι ≫ (P ≫ Q))
        exact hproperTransport'.trans hproperMove
      constructor
      · rintro ⟨t, ht, hg⟩
        let Sg := SmallEtale.supportSection B Y.obj Y.property
          fBang.obj.left VY t
        have hmonoF : Mono fBang.arrow := by dsimp [fBang]; infer_instance
        have hsupportMono := supportSection_eq_of_mono B Y.obj Y.property fBang.arrow VY t
        have hproperF := (fSub.property VY sx).mp ⟨t, ht⟩
        have hsupportPush := supportSection_smallEtalePushforward_eq_image
          B f F VY sx hproperF
        have hvalueSupport :
            SmallEtale.supportSection B Y.obj Y.property
                (fStar.obj F) VY (fBang.arrow.hom.app (Opposite.op VY) t) =
              SmallEtale.supportSection B Y.obj Y.property
                (fStar.obj F) VY sx := by
          exact congrArg
            (SmallEtale.supportSection B Y.obj Y.property (fStar.obj F) VY)
            ht
        have hsupportImage : Sg = P.base ''
            SmallEtale.supportSection B X.obj X.property F VX sx :=
          hsupportMono.symm.trans (hvalueSupport.trans hsupportPush)
        have hclosedImage : IsClosed (P.base ''
            (Tseq : Set ((SmallEtale.toScheme B X.obj X.property).obj VX))) := by
          change IsClosed ((B.inclusion.map
            (CategoryTheory.Limits.pullback.fst VY.obj.hom f)).base ''
              SmallEtale.supportSection B X.obj X.property F VX sx)
          rw [← hsupportPush]
          exact (SmallEtale.zeroOpen B Y.obj Y.property
            (fStar.obj F) VY sx).isOpen.isClosed_compl
        let Timage : TopologicalSpace.Closeds
            ((SmallEtale.toScheme B Y.obj Y.property).obj VY) :=
          ⟨P.base '' (Tseq : Set ((SmallEtale.toScheme B X.obj X.property).obj VX)),
            hclosedImage⟩
        have hTimage : Timage =
            ⟨Sg, (SmallEtale.zeroOpen B Y.obj Y.property
              fBang.obj.left VY t).isOpen.isClosed_compl⟩ := by
          apply TopologicalSpace.Closeds.ext
          change (P.base ''
            SmallEtale.supportSection B X.obj X.property F VX sx) = Sg
          exact hsupportImage.symm
        have hproperP : IsProperOver P Tseq := by
          change SmallEtale.properSupportSections B f F VY sx
          exact hproperF
        have hproperQ : IsProperOver Q Timage := by
          rw [hTimage]
          exact hg
        have hproperSeq := (hproperCompSeq).mpr
          ⟨hproperP, hclosedImage, hproperQ⟩
        change IsProperOver R Tcomp
        exact htransportSeq.mpr hproperSeq
      · intro hproperComp
        have hproperSeq : IsProperOver (P ≫ Q) Tseq :=
          htransportSeq.mp hproperComp
        rcases hproperCompSeq.mp hproperSeq with
          ⟨hproperP, hclosedImage, hproperImage⟩
        have hproperFromP : SmallEtale.properSupportSections B f F VY sx := by
          change IsProper ((Scheme.IdealSheafData.vanishingIdeal Tseq).subschemeι ≫ P)
          exact hproperP
        obtain ⟨t, ht⟩ := (fSub.property VY sx).mpr hproperFromP
        let Sg := SmallEtale.supportSection B Y.obj Y.property
          fBang.obj.left VY t
        have hmonoF : Mono fBang.arrow := by dsimp [fBang]; infer_instance
        have hsupportMono := supportSection_eq_of_mono B Y.obj Y.property fBang.arrow VY t
        have hsupportPush := supportSection_smallEtalePushforward_eq_image
          B f F VY sx hproperFromP
        have hvalueSupport :
            SmallEtale.supportSection B Y.obj Y.property
                (fStar.obj F) VY (fBang.arrow.hom.app (Opposite.op VY) t) =
              SmallEtale.supportSection B Y.obj Y.property
                (fStar.obj F) VY sx := by
          exact congrArg
            (SmallEtale.supportSection B Y.obj Y.property (fStar.obj F) VY)
            ht
        have hsupportImage : Sg = P.base ''
            SmallEtale.supportSection B X.obj X.property F VX sx :=
          hsupportMono.symm.trans (hvalueSupport.trans hsupportPush)
        have hTimage :
            (⟨P.base '' (Tseq : Set ((SmallEtale.toScheme B X.obj X.property).obj VX)),
                hclosedImage⟩ :
              TopologicalSpace.Closeds ((SmallEtale.toScheme B Y.obj Y.property).obj VY)) =
            ⟨Sg, (SmallEtale.zeroOpen B Y.obj Y.property
              fBang.obj.left VY t).isOpen.isClosed_compl⟩ := by
          apply TopologicalSpace.Closeds.ext
          change (P.base ''
            SmallEtale.supportSection B X.obj X.property F VX sx) = Sg
          exact hsupportImage.symm
        have hproperG : SmallEtale.properSupportSections B g fBang.obj.left V t := by
          change IsProperOver Q
            ⟨Sg, (SmallEtale.zeroOpen B Y.obj Y.property
              fBang.obj.left VY t).isOpen.isClosed_compl⟩
          rw [← hTimage]
          exact hproperImage
        exact ⟨t, ht, hproperG⟩
    have hrj : (∃ y, j.hom.app U y = x) ↔
        SmallEtale.properSupportSections B (f ≫ g) F V x := by
      simpa [j, fgBang] using
        (SmallEtale.fShriekSubsheaf B (f ≫ g) F).property V x
    exact hri.trans hcompSupport |>.trans hrj.symm
  let e := isoOfRangeEq i j hrange
  refine ⟨e.val, ?_⟩
  change e.val.hom ≫ fgBang.arrow =
    gBang.arrow ≫ gStar.map fBang.arrow ≫ (d.app F).hom
  exact e.property

/-- The canonical comparison is natural in the abelian étale sheaf. -/
@[stacks 0F50]
public noncomputable def properSupportFunctor_compIso
    [IsSeparated (B.inclusion.map f)] [IsSeparated (B.inclusion.map g)] :
    letI : LocallyOfFiniteType (B.inclusion.map (f ≫ g)) :=
      by rw [Functor.map_comp]; infer_instance
    { e : properSupportFunctor B f ⋙ properSupportFunctor B g ≅
          properSupportFunctor B (f ≫ g) //
      ∀ F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v},
        e.app F = (properSupportSheaf_compIso B f g F).val } := by
  letI : LocallyOfFiniteType (B.inclusion.map (f ≫ g)) := by
    rw [Functor.map_comp]
    infer_instance
  refine ⟨NatIso.ofComponents (fun F => (properSupportSheaf_compIso B f g F).val) ?_, ?_⟩
  · intro F H φ
    let fBF := (SmallEtale.fShriekSubsheaf B f F).val
    let fBH := (SmallEtale.fShriekSubsheaf B f H).val
    let gBF := (SmallEtale.fShriekSubsheaf B g fBF.obj.left).val
    let gBH := (SmallEtale.fShriekSubsheaf B g fBH.obj.left).val
    let fgBF := (SmallEtale.fShriekSubsheaf B (f ≫ g) F).val
    let fgBH := (SmallEtale.fShriekSubsheaf B (f ≫ g) H).val
    let gStar := (smallEtaleBaseChange B g).sheafPushforwardContinuous
      AddCommGrpCat.{v} (SmallEtale.topology B Z.obj Z.property)
        (SmallEtale.topology B Y.obj Y.property)
    let d := Functor.sheafPushforwardContinuousComp'
      (smallEtaleBaseChange_compIso B X Y Z f g).val
      AddCommGrpCat.{v} (SmallEtale.topology B Z.obj Z.property)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)
    let mf := SmallEtale.fShriekMap B f F H φ
    let mg := SmallEtale.fShriekMap B g
      fBF.obj.left fBH.obj.left mf.val
    let mfg := SmallEtale.fShriekMap B (f ≫ g) F H φ
    have hf := mf.property
    have hg := mg.property
    have hfg := mfg.property
    have hF := (properSupportSheaf_compIso B f g F).property
    have hH := (properSupportSheaf_compIso B f g H).property
    have hd := d.hom.naturality φ
    apply (cancel_mono ((SmallEtale.fShriekSubsheaf B (f ≫ g) H).val.arrow)).1
    change mg.val ≫ (properSupportSheaf_compIso B f g H).val.hom ≫ fgBH.arrow =
      (properSupportSheaf_compIso B f g F).val.hom ≫ mfg.val ≫ fgBH.arrow
    have hcalc :
      mg.val ≫ (properSupportSheaf_compIso B f g H).val.hom ≫ fgBH.arrow =
          (properSupportSheaf_compIso B f g F).val.hom ≫ mfg.val ≫ fgBH.arrow := by
      calc
        mg.val ≫ (properSupportSheaf_compIso B f g H).val.hom ≫ fgBH.arrow =
            mg.val ≫ (gBH.arrow ≫ gStar.map fBH.arrow ≫ (d.app H).hom) := by
              rw [hH]
        _ = (gBF.arrow ≫ gStar.map mf.val) ≫ gStar.map fBH.arrow ≫
          (d.app H).hom := by
            rw [← Category.assoc, hg]
        _ = gBF.arrow ≫ (gStar.map mf.val ≫ gStar.map fBH.arrow) ≫
          (d.app H).hom := by cat_disch
        _ = gBF.arrow ≫ gStar.map (mf.val ≫ fBH.arrow) ≫ (d.app H).hom := by
            rw [← Functor.map_comp]
        _ = gBF.arrow ≫ gStar.map (fBF.arrow ≫
          ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{v}
            (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B X.obj X.property)).map φ) ≫ (d.app H).hom := by
            rw [hf]
        _ = gBF.arrow ≫ gStar.map fBF.arrow ≫
          ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{v}
            (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B X.obj X.property) ⋙ gStar).map φ ≫
              (d.app H).hom := by
            simp only [Functor.map_comp]
            cat_disch
        _ = gBF.arrow ≫ gStar.map fBF.arrow ≫ (d.app F).hom ≫
          ((smallEtaleBaseChange B (f ≫ g)).sheafPushforwardContinuous AddCommGrpCat.{v}
            (SmallEtale.topology B Z.obj Z.property)
            (SmallEtale.topology B X.obj X.property)).map φ := by
            calc
              _ = (gBF.arrow ≫ gStar.map fBF.arrow) ≫
                  (((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{v}
                    (SmallEtale.topology B Y.obj Y.property)
                    (SmallEtale.topology B X.obj X.property) ⋙ gStar).map φ ≫
                      (d.app H).hom) := by cat_disch
              _ = (gBF.arrow ≫ gStar.map fBF.arrow) ≫
                  ((d.app F).hom ≫
                    ((smallEtaleBaseChange B (f ≫ g)).sheafPushforwardContinuous
                      AddCommGrpCat.{v} (SmallEtale.topology B Z.obj Z.property)
                      (SmallEtale.topology B X.obj X.property)).map φ) := by
                    exact congrArg (fun k =>
                      (gBF.arrow ≫ gStar.map fBF.arrow) ≫ k) hd
              _ = _ := by cat_disch
        _ = ((properSupportSheaf_compIso B f g F).val.hom ≫ fgBF.arrow) ≫
          ((smallEtaleBaseChange B (f ≫ g)).sheafPushforwardContinuous AddCommGrpCat.{v}
            (SmallEtale.topology B Z.obj Z.property)
            (SmallEtale.topology B X.obj X.property)).map φ := by
            calc
              _ = (gBF.arrow ≫ gStar.map fBF.arrow ≫ (d.app F).hom) ≫
                  ((smallEtaleBaseChange B (f ≫ g)).sheafPushforwardContinuous
                    AddCommGrpCat.{v} (SmallEtale.topology B Z.obj Z.property)
                    (SmallEtale.topology B X.obj X.property)).map φ := by cat_disch
              _ = ((properSupportSheaf_compIso B f g F).val.hom ≫ fgBF.arrow) ≫
                  ((smallEtaleBaseChange B (f ≫ g)).sheafPushforwardContinuous
                    AddCommGrpCat.{v} (SmallEtale.topology B Z.obj Z.property)
                    (SmallEtale.topology B X.obj X.property)).map φ := by
                    exact congrArg (fun k => k ≫
                      ((smallEtaleBaseChange B (f ≫ g)).sheafPushforwardContinuous
                        AddCommGrpCat.{v} (SmallEtale.topology B Z.obj Z.property)
                        (SmallEtale.topology B X.obj X.property)).map φ) hF.symm
        _ = ((properSupportSheaf_compIso B f g F).val.hom) ≫
          (mfg.val ≫ fgBH.arrow) := by
            exact congrArg
              (fun k => (properSupportSheaf_compIso B f g F).val.hom ≫ k) hfg.symm
        _ = (properSupportSheaf_compIso B f g F).val.hom ≫ mfg.val ≫ fgBH.arrow := by cat_disch
    exact hcalc
  · intro F
    rfl

end AlgebraicGeometry.SmallEtale
