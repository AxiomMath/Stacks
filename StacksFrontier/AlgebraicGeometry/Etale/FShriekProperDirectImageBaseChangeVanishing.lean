module

public import StacksFrontier.AlgebraicGeometry.Etale.ProperBaseChangeHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenCover
public import StacksFrontier.AlgebraicGeometry.Etale.ProperLowerShriekBaseChangePullback
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Higher direct images of `k_! J` along a proper morphism, for a square of proper and
# quasi-finite morphisms

Consider a commutative square of a big étale site
```
X' --k--> X
|         |
f'        f
v         v
Y' --l--> Y
```
with `f`, `f'` proper and `k`, `l` separated and locally quasi-finite, and a torsion abelian
sheaf `J` on `X'_étale` with `R^q f'_* J = 0` for `q > 0`. Then

`R^q f_* (k_! J) = 0` for `q > 0`.

This is the vanishing in the proof of [Stacks, Tag 0F7B] (applied there to an injective sheaf
`J`, over a torsion ring). The proof is the source's. Vanishing of `R^q f_* (k_! J)` is detected
after inverse image to the residue fields of `Y`, and by proper base change ([Stacks, Tag 095T])
and the base change of `k_!` ([Stacks, Tag 0F55]) the inverse image to `Spec κ(y)` is
`R^q f_{y,*}(k_{y,!} J_y)` for the base changed square over `Spec κ(y)`, in which
`R^q f'_{y,*} J_y = 0` still holds. Over a field `Y'` is discrete; `X'` is the directed union of
the preimages `X'_W` of the finite subsets `W` of `Y'`, and `k_! J` is the filtered colimit of the
`(k_W)_! (J|_{X'_W})` ([Stacks, Tag 0F54]). Each `k_W : X'_W ⟶ X` is proper and quasi-finite,
hence finite, so `(k_W)_! = (k_W)_*` ([Stacks, Tag 0F51]) and
`R^q f_*((k_W)_* J_W) = R^q (f ∘ k_W)_* J_W = (l_W)_* R^q f'_{W,*} J_W = 0`, the morphism
`l_W : W ⟶ Y` being finite. Higher direct images commute with filtered colimits.

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_etalePushforward_fShriekFunctor_of_field`:
  the vanishing over the spectrum of a field.
* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_etalePushforward_fShriekFunctor_of_square`:
  the vanishing.

## References

* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 0F54](https://stacks.math.columbia.edu/tag/0F54)
* [Stacks Project, Tag 0F55](https://stacks.math.columbia.edu/tag/0F55)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

attribute [local instance] SmallEtale.isGrothendieckAbelian_sheaf_succ

variable (B : BigEtaleSite.{u})

/-! ### Finite subsets of a discrete object -/

section Discrete

variable {T : B.Scheme} [DiscreteTopology T.obj]

/-- The open subscheme of a discrete object on a finite set of its points. -/
def finsetOpens (F : Finset (ULift.{u + 1} T.obj)) : T.obj.Opens :=
  ⟨{t | ULift.up t ∈ F}, isOpen_discrete _⟩

/-- The open subscheme on a finite set of points, as an object of the big étale site. -/
abbrev finsetObj (F : Finset (ULift.{u + 1} T.obj)) : B.Scheme :=
  B.obj (finsetOpens B F) (Scheme.size_lt_of_isOpenImmersion (finsetOpens B F).ι T.property)

/-- The inclusion of the open subscheme on a finite set of points. -/
abbrev finsetι (F : Finset (ULift.{u + 1} T.obj)) : finsetObj B F ⟶ T :=
  ObjectProperty.homMk (finsetOpens B F).ι

/-- The inclusion of the open subscheme on a finite set of points is an open immersion. -/
private instance isOpenImmersion_inclusion_map_finsetι (F : Finset (ULift.{u + 1} T.obj)) :
    IsOpenImmersion (B.inclusion.map (finsetι B F)) :=
  inferInstanceAs (IsOpenImmersion (finsetOpens B F).ι)

/-- The open subscheme on a finite set of points is monotone in the finite set. -/
lemma finsetOpens_mono {F G : Finset (ULift.{u + 1} T.obj)} (h : F ≤ G) :
    finsetOpens B F ≤ finsetOpens B G :=
  fun _ ht => h ht

/-- The inclusion of the open subscheme on a smaller finite set into that on a larger one. -/
abbrev finsetHomOfLE {F G : Finset (ULift.{u + 1} T.obj)} (h : F ≤ G) :
    finsetObj B F ⟶ finsetObj B G :=
  ObjectProperty.homMk (T.obj.homOfLE (finsetOpens_mono B h))

/-- The inclusion `finsetHomOfLE` commutes with the inclusions into `T`. -/
@[reassoc (attr := simp)]
lemma finsetHomOfLE_ι {F G : Finset (ULift.{u + 1} T.obj)} (h : F ≤ G) :
    finsetHomOfLE B h ≫ finsetι B G = finsetι B F :=
  ObjectProperty.hom_ext _ (Scheme.homOfLE_ι T.obj (finsetOpens_mono B h))

/-- The open subschemes on the finite sets of points, as a functor to objects over `T`. -/
def finsetOverFunctor : Finset (ULift.{u + 1} T.obj) ⥤ Over T where
  obj F := Over.mk (finsetι B F)
  map h := Over.homMk (finsetHomOfLE B h.le) (finsetHomOfLE_ι B h.le)
  map_id _ := Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Scheme.homOfLE_rfl T.obj _))
  map_comp h₁ h₂ := Over.OverMorphism.ext (ObjectProperty.hom_ext _
    (Scheme.homOfLE_homOfLE T.obj (finsetOpens_mono B h₁.le) (finsetOpens_mono B h₂.le)).symm)

end Discrete

/-! ### Over the spectrum of a field -/

section Field

/-- A colimit of zero objects is zero. -/
lemma isZero_pt_of_isColimit {C J : Type*} [Category* C] [Category* J] [HasZeroMorphisms C]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) (h : ∀ j, IsZero (D.obj j)) : IsZero c.pt :=
  (IsZero.iff_id_eq_zero _).2 (hc.hom_ext fun j => (h j).eq_of_src _ _)

variable {R : CommRingCat.{u}} (hR : IsField R) (hK : B.Contains (Spec R))

include hR hK in
/-- An object locally quasi-finite over the spectrum of a field is discrete. -/
theorem discreteTopology_of_locallyQuasiFinite_field {T : B.Scheme} (l : T ⟶ B.obj _ hK)
    [LocallyQuasiFinite (B.inclusion.map l)] : DiscreteTopology T.obj := by
  let := hR.toField
  have : Subsingleton (B.inclusion.obj (B.obj _ hK)) :=
    inferInstanceAs (Subsingleton (Spec (.of R)))
  rcases isEmpty_or_nonempty T.obj with hT | ⟨⟨t⟩⟩
  · exact ⟨Subsingleton.elim _ _⟩
  · have hpre : (B.inclusion.map l).base ⁻¹' {(B.inclusion.map l).base t} = Set.univ :=
      Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
    have hdisc := (B.inclusion.map l).isDiscrete_preimage_singleton ((B.inclusion.map l).base t)
    rwa [hpre, isDiscrete_univ_iff] at hdisc

variable {X X' T : B.Scheme} (f : X ⟶ B.obj _ hK) (l : T ⟶ B.obj _ hK) (f' : X' ⟶ T)
  (k : X' ⟶ X) (w : k ≫ f = f' ≫ l)

include hR in
/-- The inclusion of a finite set of points of `T`, followed by a locally quasi-finite
`l : T ⟶ Spec R` over a field `R`, is finite. -/
private theorem isFinite_finsetι_comp_of_field [DiscreteTopology T.obj]
    [LocallyQuasiFinite (B.inclusion.map l)] (F : Finset (ULift.{u + 1} T.obj)) :
    IsFinite (B.inclusion.map (finsetι B F ≫ l)) := by
  let := hR.toField
  have : Finite (B.inclusion.obj (finsetObj B F)) :=
    ((F.finite_toSet.preimage ULift.up_injective.injOn).to_subtype :)
  have : CompactSpace (B.inclusion.obj (finsetObj B F)) := Finite.compactSpace
  have : QuasiSeparatedSpace (B.inclusion.obj (B.obj _ hK)) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec R))
  have : QuasiCompact (B.inclusion.map (finsetι B F ≫ l)) := quasiCompact_of_compactSpace _
  have : LocallyQuasiFinite (B.inclusion.map (finsetι B F ≫ l)) := by
    rw [Functor.map_comp]
    infer_instance
  have : IsLocallyArtinian (B.inclusion.obj (B.obj _ hK)) :=
    inferInstanceAs (IsLocallyArtinian (Spec R))
  exact IsFinite.of_locallyQuasiFinite _

/-- Proper base change: if `R^q f'_* J = 0` for a proper `f'` and a torsion sheaf `J`, then
`R^q f₁_* (a⁻¹ J) = 0` for the base change `f₁` of `f'` along `b`. -/
private theorem isZero_rightDerived_etalePushforward_abPullback_obj {X Y X₁ Y₁ : B.Scheme}
    (a : X₁ ⟶ X) (f₁ : X₁ ⟶ Y₁) (f : X ⟶ Y) (b : Y₁ ⟶ Y) (sq : IsPullback a f₁ f b)
    [IsProper (B.inclusion.map f)]
    (J : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hJ : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X.obj X.property) J)
    (q : ℕ) (h : IsZero (((etalePushforward.{u, u + 1} B f).rightDerived q).obj J)) :
    IsZero (((etalePushforward.{u, u + 1} B f₁).rightDerived q).obj
      ((abPullback.{u, 0} B a).obj J)) := by
  have := additive_abPullback.{u, 0} B b
  have : (abPullback.{u, 0} B b).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  exact ((abPullback.{u, 0} B b).map_isZero h).of_iso
    (abPullbackRightDerivedEtalePushforwardIsoOfIsProper B a f₁ f b sq J hJ q).symm

include w in
/-- One stage of the colimit: for an open `b : W ⟶ T` finite over `Spec R`, with
`a : X'_W = W ×_T X' ⟶ X'`, the morphism `a ≫ k` is finite and
`R^q f_*((a ≫ k)_! (a⁻¹ J)) = R^q f_*((a ≫ k)_* (a⁻¹ J)) = (b ≫ l)_* R^q f'_{W,*}(a⁻¹ J) = 0`. -/
theorem isZero_rightDerived_etalePushforward_properSupportFunctor_stage
    [IsProper (B.inclusion.map f)] [IsProper (B.inclusion.map f')]
    [LocallyQuasiFinite (B.inclusion.map k)] [LocallyOfFiniteType (B.inclusion.map k)]
    {W P : B.Scheme} (b : W ⟶ T) [IsOpenImmersion (B.inclusion.map b)]
    [IsFinite (B.inclusion.map (b ≫ l))] (a : P ⟶ X') (f₁ : P ⟶ W)
    (sq : IsPullback a f₁ f' b) [LocallyOfFiniteType (B.inclusion.map (a ≫ k))]
    (J : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1})
    (hJ : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X'.obj X'.property) J)
    (hJ' : ∀ q : ℕ, 0 < q → IsZero (((etalePushforward.{u, u + 1} B f').rightDerived q).obj J))
    (q : ℕ) (hq : 0 < q) :
    IsZero (((etalePushforward.{u, u + 1} B f).rightDerived q).obj
      ((properSupportFunctor.{u, u + 1} B (a ≫ k)).obj ((abPullback.{u, 0} B a).obj J))) := by
  have : IsOpenImmersion (B.inclusion.map a) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (sq.flip.map B.inclusion) inferInstance
  have : LocallyQuasiFinite (B.inclusion.map (a ≫ k)) := by
    rw [Functor.map_comp]
    infer_instance
  have h1 : (a ≫ k) ≫ f = f₁ ≫ (b ≫ l) := by
    rw [Category.assoc, w, ← Category.assoc, sq.w, Category.assoc]
  have : IsProper (B.inclusion.map f₁) := isProper_of_isPullback B a f₁ f' b sq
  have : IsProper (B.inclusion.map (a ≫ k)) := by
    have : IsProper (B.inclusion.map (a ≫ k) ≫ B.inclusion.map f) := by
      rw [← Functor.map_comp, h1, Functor.map_comp]
      infer_instance
    exact IsProper.of_comp _ (B.inclusion.map f)
  have : IsFinite (B.inclusion.map (a ≫ k)) := IsFinite.of_isProper_of_locallyQuasiFinite _
  let M := (abPullback.{u, 0} B a).obj J
  have hM : IsZero (((etalePushforward.{u, u + 1} B f₁).rightDerived q).obj M) :=
    isZero_rightDerived_etalePushforward_abPullback_obj B a f₁ f' b sq J hJ q (hJ' q hq)
  have h2 : IsZero (((etalePushforward.{u, u + 1} B ((a ≫ k) ≫ f)).rightDerived q).obj M) := by
    rw [h1]
    exact ((etalePushforward.{u, u + 1} B (b ≫ l)).map_isZero hM).of_iso
      ((rightDerivedEtalePushforwardCompIsoOfIsFinite' B f₁ (b ≫ l) q).app M).symm
  exact (h2.of_iso
      ((rightDerivedEtalePushforwardCompIsoOfIsFinite B (a ≫ k) f q).app M).symm).of_iso
    (((etalePushforward.{u, u + 1} B f).rightDerived q).mapIso
      ((properSupportIsoPushforward.{u, u + 1} B (a ≫ k)).app M))

include hR w in
/-- **`R^q f_* (k_! J) = 0` for `q > 0` over the spectrum of a field.** For a commutative
square `k ≫ f = f' ≫ l` of a big étale site over `Spec R`, `R` a field, with `f`, `f'` proper,
`k`, `l` separated and locally quasi-finite, and a torsion abelian sheaf `J` on `X'_étale` with
`R^q f'_* J = 0` for `q > 0`. The object `T` is discrete, `X'` is the directed union of the
preimages `X'_W` of the finite subsets `W` of `T`, over which `k` is finite; so `k_! J` is the
filtered colimit of the `(k_W)_* (J|_{X'_W})` ([Stacks, Tag 0F54], [Stacks, Tag 0F51]), and
`R^q f_*((k_W)_* J_W) = (l_W)_* R^q f'_{W,*} J_W` vanishes by proper base change. -/
theorem isZero_rightDerived_etalePushforward_fShriekFunctor_of_field
    [IsProper (B.inclusion.map f)] [IsProper (B.inclusion.map f')]
    [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
    [LocallyOfFiniteType (B.inclusion.map k)]
    [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
    (J : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1})
    (hJ : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X'.obj X'.property) J)
    (hJ' : ∀ q : ℕ, 0 < q → IsZero (((etalePushforward.{u, u + 1} B f').rightDerived q).obj J))
    (q : ℕ) (hq : 0 < q) :
    IsZero (((etalePushforward.{u, u + 1} B f).rightDerived q).obj
      ((fShriekFunctor.{u, u} B k).obj J)) := by
  have := discreteTopology_of_locallyQuasiFinite_field B hR hK l
  let ι := Finset (ULift.{u + 1} T.obj)
  let U : ι ⥤ B.Scheme := finsetOverFunctor B ⋙ Over.pullback f' ⋙ Over.forget X'
  let j : U ⟶ (Functor.const ι).obj X' :=
    Functor.whiskerLeft (finsetOverFunctor B ⋙ Over.pullback f') (Over.forgetCocone X').ι
  have hj : ∀ F, j.app F = pullback.snd (finsetι B F) f' := fun _ => rfl
  have hopen : ∀ F, IsOpenImmersion (B.inclusion.map (j.app F)) := fun F => by
    rw [hj]
    have sq := (IsPullback.of_hasPullback (finsetι B F) f').map B.inclusion
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq inferInstance
  have hcover : ∀ x : X'.obj, ∃ F, x ∈ Set.range (B.inclusion.map (j.app F)).base := by
    intro x
    refine ⟨{ULift.up ((B.inclusion.map f').base x)}, ?_⟩
    rw [hj]
    let y : (finsetOpens B ({ULift.up ((B.inclusion.map f').base x)} : ι)).toScheme :=
      ⟨(B.inclusion.map f').base x, Finset.mem_singleton_self _⟩
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := B.inclusion.map (finsetι B _)) (g := B.inclusion.map f') y x rfl
    refine ⟨(PreservesPullback.iso B.inclusion (finsetι B _) f').inv.base z, ?_⟩
    have e := congrArg (fun g => g z) (PreservesPullback.iso_inv_snd B.inclusion (finsetι B _) f')
    simp only [Scheme.Hom.comp_apply] at e
    exact e.trans hz
  obtain ⟨D, c, hpt, hD, ⟨hc⟩⟩ :=
    properSupportFunctor_isColimit_openCover.{u, u + 1} B k U j hopen hcover
  let RD := (etalePushforward.{u, u + 1} B f).rightDerived q
  have : IsFiltered ι := isFiltered_of_directed_le_nonempty ι
  have : UniversallyClosed (B.inclusion.map f) := IsProper.toUniversallyClosed
  have : QuasiCompact (B.inclusion.map f) := instQuasiCompactOfUniversallyClosed _
  have : IsSeparated (B.inclusion.map f) := IsProper.toIsSeparated
  have : QuasiSeparated (B.inclusion.map f) := IsSeparated.instQuasiSeparated _
  have := preservesColimitsOfShape_rightDerived_etalePushforward B f q ι
  have hz : ∀ F : ι, IsZero ((D ⋙ ((evaluation _ _).obj J) ⋙ RD).obj F) := by
    intro F
    obtain ⟨hi, -⟩ := hD F
    change IsZero (RD.obj ((D.obj F).obj J))
    rw [hi]
    have := isFinite_finsetι_comp_of_field B hR hK l F
    exact isZero_rightDerived_etalePushforward_properSupportFunctor_stage B hK f l f' k w
      (finsetι B F) (j.app F) (pullback.fst _ _)
      (IsPullback.of_hasPullback _ _).flip J hJ hJ' q hq
  have h0 := isZero_pt_of_isColimit (isColimitOfPreserves ((evaluation _ _).obj J ⋙ RD) hc) hz
  change IsZero (RD.obj (c.pt.obj J)) at h0
  rw [hpt] at h0
  exact h0.of_iso (RD.mapIso ((fShriekFunctorIsoProperSupport.{u, u} B k).app J))

end Field

/-! ### The general case -/

section Square

variable {X' X Y' Y : B.Scheme} (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y)
  (w : k ≫ f = f' ≫ l)

include w in
/-- **`R^q f_* (k_! J) = 0` for `q > 0`** ([Stacks, Tag 0F7B], the vanishing in its proof). Let
`k ≫ f = f' ≫ l` be a commutative square of a big étale site with `f`, `f'` proper and `k`, `l`
separated and locally quasi-finite, and let `J` be a torsion abelian sheaf on `X'_étale` with
`R^q f'_* J = 0` for `q > 0`. Then `R^q f_* (k_! J) = 0` for `q > 0`.

Vanishing is detected on the inverse images to the residue fields `Spec κ(y)` of `Y`
(`AlgebraicGeometry.SmallEtale.isZero_of_forall_isZero_abPullback_residueFieldHom`). There,
proper base change ([Stacks, Tag 095T],
`AlgebraicGeometry.SmallEtale.abPullbackRightDerivedEtalePushforwardIsoOfIsProper`) and the base
change of `k_!` ([Stacks, Tag 0F55]) identify the inverse image of `R^q f_* (k_! J)` with
`R^q f_{y,*}(k_{y,!} J_y)` for the base changed square over `Spec κ(y)`, which vanishes by
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_etalePushforward_fShriekFunctor_of_field`; its
hypothesis `R^q f'_{y,*} J_y = 0` is again proper base change. -/
theorem isZero_rightDerived_etalePushforward_fShriekFunctor_of_square
    [IsProper (B.inclusion.map f)] [IsProper (B.inclusion.map f')]
    [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
    [LocallyOfFiniteType (B.inclusion.map k)]
    [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map l)]
    (J : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1})
    (hJ : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X'.obj X'.property) J)
    (hJ' : ∀ q : ℕ, 0 < q → IsZero (((etalePushforward.{u, u + 1} B f').rightDerived q).obj J))
    (q : ℕ) (hq : 0 < q) :
    IsZero (((etalePushforward.{u, u + 1} B f).rightDerived q).obj
      ((fShriekFunctor.{u, u} B k).obj J)) := by
  refine isZero_of_forall_isZero_abPullback_residueFieldHom B _ fun y => ?_
  let S := residueFieldObj B y
  let b : S ⟶ Y := residueFieldHom B y
  let a := pullback.fst f b
  let fy := pullback.snd f b
  have sqX : IsPullback a fy f b := IsPullback.of_hasPullback f b
  let p := pullback.fst k a
  let ky := pullback.snd k a
  have sqK : IsPullback p ky k a := IsPullback.of_hasPullback k a
  let ly := pullback.snd l b
  have sqY : IsPullback (pullback.fst l b) ly l b := IsPullback.of_hasPullback l b
  have hc : (p ≫ f') ≫ l = (ky ≫ fy) ≫ b := by
    rw [Category.assoc, ← w, ← Category.assoc, sqK.w, Category.assoc, sqX.w, Category.assoc]
  let f'y : pullback k a ⟶ pullback l b := pullback.lift (p ≫ f') (ky ≫ fy) hc
  have wy : ky ≫ fy = f'y ≫ ly := (pullback.lift_snd _ _ _).symm
  have sqF : IsPullback p f'y f' (pullback.fst l b) := by
    have H := sqK.paste_vert sqX
    rw [w, wy] at H
    exact IsPullback.of_bot H (pullback.lift_fst _ _ _).symm sqY
  have : IsProper (B.inclusion.map fy) := isProper_of_isPullback B a fy f b sqX
  have : IsProper (B.inclusion.map f'y) := isProper_of_isPullback B p f'y f' _ sqF
  have := isSeparated_of_isPullback B p ky k a sqK
  have := locallyQuasiFinite_of_isPullback B p ky k a sqK
  have := locallyOfFiniteType_of_isPullback B p ky k a sqK
  have := isSeparated_of_isPullback B _ ly l b sqY
  have := locallyQuasiFinite_of_isPullback B _ ly l b sqY
  let Jy := (abPullback.{u, 0} B p).obj J
  have hJy' : ∀ q : ℕ, 0 < q →
      IsZero (((etalePushforward.{u, u + 1} B f'y).rightDerived q).obj Jy) := fun q hq =>
    isZero_rightDerived_etalePushforward_abPullback_obj B p f'y f' _ sqF J hJ q (hJ' q hq)
  exact (isZero_rightDerived_etalePushforward_fShriekFunctor_of_field B
      (Field.toIsField (Y.obj.residueField y)) (contains_spec_residueField B y) fy ly f'y ky wy
      Jy (torsionSheafProperty_abPullback_obj B p J hJ) hJy' q hq).of_iso
    (abPullbackRightDerivedEtalePushforwardIsoOfIsProper B a fy f b sqX _
        (torsionSheafProperty_fShriekFunctor_obj.{u, u} B k J hJ) q ≪≫
      ((etalePushforward.{u, u + 1} B fy).rightDerived q).mapIso
        ((fShriekProperSupportBaseChangeIso B p ky k a sqK).app J))

end Square

end AlgebraicGeometry.SmallEtale

end
