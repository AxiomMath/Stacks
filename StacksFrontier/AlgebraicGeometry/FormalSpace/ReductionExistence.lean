module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Assembly.Relativize
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReductionSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalChartRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescentFromFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleQuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Descent
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds
import all StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas

/-!
# The reduction of a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `X` be a formal algebraic space
over `S`. **Stacks 0AIN** asserts that `X` has a *reduction*: a reduced algebraic space `X_red`
together with a representable morphism `X_red ⟶ X` which is a thickening, and through which
every morphism to `X` from a reduced algebraic space factors uniquely. This file proves it for
an arbitrary formal algebraic space. The affine case is
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isAffineFormalAlgebraicSpace`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`: every formal
  algebraic space has a reduction.

## References

* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Thickenings: fppf locality and the coarser descent property -/

/-- Being a thickening is fppf local on the target. -/
theorem isThickening_isLocalAtTarget_fppf :
    (show MorphismProperty Scheme.{u} from @Stacks.Thickenings.IsThickening).IsLocalAtTarget
      Scheme.fppfPrecoverage := by
  have := Stacks.Thickenings.isThickening_isLocalAtTarget_fpqc.{u}
  exact MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage

/-- A thickening of schemes is separated, locally quasi-finite and locally of finite type. -/
theorem isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_of_isThickening
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : Stacks.Thickenings.IsThickening f) :
    (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
      MorphismProperty Scheme.{u}) f := by
  have : IsClosedImmersion f := hf.1
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

/-- A relative property of a morphism of presheaves is monotone in the property. -/
private theorem presheaf_mono_of_le {P Q : MorphismProperty Scheme.{u}}
    (hPQ : ∀ {V W : Scheme.{u}} (f : V ⟶ W), P f → Q f)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f :=
  ⟨hf.rep, fun _ _ g fst snd hpb => hPQ _ (hf.property g fst snd hpb)⟩

/-! ### Lifting along the reduction of an object of the site -/

/-- A morphism from a reduced object of the site into the target of a thickening of objects of
the site lifts along the thickening. -/
theorem exists_lift_siteReduction_of_isReduced
    {V T W : BigFppfOver B S hS} (r : V ⟶ T)
    (hr : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map r))
    (hW : IsReduced ((BigFppfOver.toScheme B S hS).obj W))
    (f : W ⟶ T) : ∃ g : W ⟶ V, g ≫ r = f := by
  have hpb := (IsPullback.of_hasPullback r f).map (BigFppfOver.toScheme B S hS)
  have hp : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (pullback.snd r f)) :=
    isThickening_isStableUnderBaseChange.of_isPullback hpb hr
  have := hp.1
  have : Surjective ((BigFppfOver.toScheme B S hS).map (pullback.snd r f)) := ⟨hp.2⟩
  have := isIso_of_isClosedImmersion_of_surjective
    ((BigFppfOver.toScheme B S hS).map (pullback.snd r f))
  have : IsIso (pullback.snd r f) :=
    isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)
  refine ⟨inv (pullback.snd r f) ≫ pullback.fst r f, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
    Category.id_comp]

/-- An object of the site whose reduction map is locally surjective is already reduced. -/
theorem isReduced_of_isLocallySurjective_siteReductionMap (T : BigFppfOver B S hS)
    (hs : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (uliftYoneda.{u + 1}.map (siteReductionMap B S hS T))) :
    IsReduced ((BigFppfOver.toScheme B S hS).obj T) := by
  let J := BigFppfOver.topology B S hS
  let Y := GrothendieckTopology.uliftYoneda.{u + 1} J
  let r := siteReductionMap B S hS T
  have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map r) :=
    (isThickening_toScheme_map_siteReductionMap B S hS T).1
  have : Mono r := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  have : Mono (Y.map r) := by
    apply (sheafToPresheaf J (Type (u + 1))).mono_of_mono_map
    change Mono (uliftYoneda.{u + 1}.map r)
    infer_instance
  have : Sheaf.IsLocallySurjective (Y.map r) := hs
  have : IsIso (Y.map r) := isIso_of_mono_of_epi _
  have : IsIso r := isIso_of_reflects_iso _ Y
  have : IsReduced ((BigFppfOver.toScheme B S hS).obj (siteReduction B S hS T)) :=
    isReduced_toScheme_obj_siteReduction B S hS T
  exact isReduced_of_isOpenImmersion (inv ((BigFppfOver.toScheme B S hS).map r))

/-! ### Gluing scheme-valued points over a disjoint open cover -/

/-- A sheaf on the big fppf site of `S` has at most one section over an object with empty
underlying scheme. -/
private theorem sections_subsingleton_of_isEmpty
    (X : FppfSheaf B S hS) (U : BigFppfOver B S hS) [IsEmpty U.left.obj] :
    Subsingleton (X.obj.obj (op U)) := by
  have hcov := fppf_ofArrows_mem B S hS (I := PEmpty.{u + 1})
    (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
    (U := U) (fun x => isEmptyElim x)
  refine ⟨fun x y => ?_⟩
  have h := X.property.hom_ext_ofArrows (fun i : PEmpty.{u + 1} => i.elim)
    hcov (x := (↾fun _ : PUnit.{u + 2} => x))
    (y := (↾fun _ : PUnit.{u + 2} => y)) (fun i => i.elim)
  exact ConcreteCategory.congr_hom h PUnit.unit

/-- A scheme-valued point of a sheaf may be glued from a family of points over a pairwise
disjoint open cover of an object of the site. -/
theorem exists_amalgamation_of_disjoint_openCover
    (X : FppfSheaf B S hS) {I : Type u} {W : BigFppfOver B S hS}
    (V : I → BigFppfOver B S hS) (k : ∀ i, V i ⟶ W)
    (hk : ∀ i, IsOpenImmersion (k i).left.hom)
    (hcov : ∀ w : W.left.obj, ∃ i, w ∈ Set.range (k i).left.hom)
    (hdisj : ∀ i j, i ≠ j → ∀ (z : (V i).left.obj) (z' : (V j).left.obj),
      (k i).left.hom z ≠ (k j).left.hom z')
    (f : ∀ i, uliftYoneda.{u + 1}.obj (V i) ⟶ X.obj) :
    ∃ q : uliftYoneda.{u + 1}.obj W ⟶ X.obj,
      ∀ i, uliftYoneda.{u + 1}.map (k i) ≫ q = f i := by
  classical
  have hmem := fppf_ofArrows_mem B S hS V k
    (fun i => by have := hk i; infer_instance)
    (fun i => by have := hk i; infer_instance) hcov
  let x (i : I) : PUnit.{u + 2} ⟶ X.obj.obj (op (V i)) :=
    ↾fun _ => uliftYonedaEquiv (f i)
  have hx : ∀ ⦃T⦄ ⦃i j⦄ (a : T ⟶ V i) (b : T ⟶ V j),
      a ≫ k i = b ≫ k j → x i ≫ X.obj.map a.op = x j ≫ X.obj.map b.op := by
    intro T i j a b hab
    by_cases hij : i = j
    · subst j
      have hm : Mono (k i).left.hom := by have := hk i; infer_instance
      have : Mono (k i).left := B.inclusion.mono_of_mono_map hm
      have : Mono (k i) := Over.mono_of_mono_left _
      rw [(cancel_mono (k i)).mp hab]
    · have hw : a.left.hom ≫ (k i).left.hom = b.left.hom ≫ (k j).left.hom :=
        congrArg (fun t : T ⟶ W => t.left.hom) hab
      have : IsEmpty T.left.obj :=
        ⟨fun z => hdisj i j hij (a.left.hom z) (b.left.hom z) (by
          rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply])⟩
      have := sections_subsingleton_of_isEmpty B S hS X T
      ext z
      exact Subsingleton.elim _ _
  obtain ⟨z, hz, -⟩ := X.property.existsUnique_amalgamation_ofArrows k hmem x hx
  refine ⟨uliftYonedaEquiv.symm (z PUnit.unit), fun i => uliftYonedaEquiv.injective ?_⟩
  exact (uliftYonedaEquiv_naturality.{u + 1}
    (uliftYonedaEquiv.symm (z PUnit.unit)) (k i).op).symm.trans
      (by simpa [x] using ConcreteCategory.congr_hom (hz i) PUnit.unit)

/-- The coproduct of a `Type u`-indexed family of objects of the site which is again small is
an object of the site, its component inclusions are pairwise disjoint open immersions covering
it, and a family of scheme-valued points of a sheaf glues to a point over it. -/
theorem exists_map_from_coproduct
    (X : FppfSheaf B S hS) {I : Type u} (V : I → BigFppfOver B S hS)
    (f : ∀ i, uliftYoneda.{u + 1}.obj (V i) ⟶ X.obj)
    (hsize : B.Contains (∐ fun i => (V i).left.obj)) :
    ∃ (W : BigFppfOver B S hS)
      (k : ∀ i, V i ⟶ W) (q : uliftYoneda.{u + 1}.obj W ⟶ X.obj),
      (∀ i, uliftYoneda.map (k i) ≫ q = f i) ∧
      (∀ i, IsOpenImmersion (k i).left.hom) ∧
      (∀ w : W.left.obj, ∃ i, w ∈ Set.range (k i).left.hom) ∧
      (∀ i j, i ≠ j → ∀ (z : (V i).left.obj) (z' : (V j).left.obj),
        (k i).left.hom z ≠ (k j).left.hom z') := by
  classical
  let D := fun i => (V i).left.obj
  let W : BigFppfOver B S hS :=
    Over.mk (Y := B.obj hsize) (X := B.obj hS) ⟨Sigma.desc (fun i => (V i).hom.hom)⟩
  let k (i : I) : V i ⟶ W :=
    Over.homMk ⟨Sigma.ι D i⟩ (ObjectProperty.hom_ext _ (Sigma.ι_comp_desc _ _))
  have hk (i : I) : IsOpenImmersion (k i).left.hom := by
    change IsOpenImmersion (Sigma.ι D i)
    infer_instance
  have hcov : ∀ w : W.left.obj, ∃ i, w ∈ Set.range (k i).left.hom :=
    (sigmaOpenCover D).exists_eq
  have hdisj : ∀ i j, i ≠ j → ∀ (z : (V i).left.obj) (z' : (V j).left.obj),
      (k i).left.hom z ≠ (k j).left.hom z' := fun i j hij z z' hz =>
    hij (congrArg Sigma.fst ((sigmaι_eq_iff D i j z z').mp hz))
  obtain ⟨q, hq⟩ := exists_amalgamation_of_disjoint_openCover B S hS X V k hk hcov hdisj f
  exact ⟨W, k, q, hq, hk, hcov, hdisj⟩

/-- The coproduct of a family of objects of the site indexed by the points of an object `a` of the
site, each of size at most that of `a`, is small. -/
private theorem contains_coproduct_of_size_le {a : BigFppfOver B S hS}
    (D : a.left.obj → BigFppfOver B S hS) (hD : ∀ x, (D x).left.obj.size ≤ a.left.obj.size) :
    B.Contains (∐ fun x => (D x).left.obj) :=
  lt_of_le_of_lt (schemeSize_coproduct_le _ (2 ^ a.left.obj.size)
    (a.left.obj.aleph0_le_size.trans (Cardinal.cantor _).le)
    (Scheme.mk_le_two_pow_size a.left.obj)
    (fun x => (hD x).trans (Cardinal.cantor _).le))
    (B.cutoff_isStrongPrelimit a.left.property)

/-- The universe-lifted Yoneda embedding of a monomorphism of site objects is a monomorphism
of presheaves. -/
theorem uliftYoneda_map_mono {V W : BigFppfOver B S hS} (p : V ⟶ W) (hp : Mono p) :
    Mono (uliftYoneda.{u + 1}.map p) :=
  (NatTrans.mono_iff_mono_app _).2 fun _ => (mono_iff_injective _).2 fun _ _ hs =>
    ULift.ext ((cancel_mono p).mp (congrArg ULift.down hs))

/-- Two scheme-valued points of a sheaf agree as soon as they agree on each member of an open
cover of the source. -/
theorem uliftYoneda_hom_ext_of_openCover (X : FppfSheaf B S hS)
    {I : Type u} {W : BigFppfOver B S hS}
    (V : I → BigFppfOver B S hS) (k : ∀ i, V i ⟶ W)
    (hk : ∀ i, IsOpenImmersion (k i).left.hom)
    (hcov : ∀ w : W.left.obj, ∃ i, w ∈ Set.range (k i).left.hom)
    (a b : uliftYoneda.{u + 1}.obj W ⟶ X.obj)
    (hab : ∀ i, uliftYoneda.{u + 1}.map (k i) ≫ a = uliftYoneda.{u + 1}.map (k i) ≫ b) :
    a = b := by
  have hmem := fppf_ofArrows_mem B S hS V k
    (fun i => by have := hk i; infer_instance)
    (fun i => by have := hk i; infer_instance) hcov
  apply uliftYonedaEquiv.injective
  refine ConcreteCategory.congr_hom (X.property.hom_ext_ofArrows k hmem
    (x := (↾fun _ : PUnit.{u + 2} => uliftYonedaEquiv.{u + 1} a))
    (y := (↾fun _ : PUnit.{u + 2} => uliftYonedaEquiv.{u + 1} b)) ?_) PUnit.unit
  intro i
  ext _
  change X.obj.map (k i).op (uliftYonedaEquiv.{u + 1} a) =
    X.obj.map (k i).op (uliftYonedaEquiv.{u + 1} b)
  rw [uliftYonedaEquiv_naturality.{u + 1} a (k i).op,
    uliftYonedaEquiv_naturality.{u + 1} b (k i).op]
  exact congrArg uliftYonedaEquiv (hab i)

/-! ### Being a pullback square is local on the base -/

/-- A commuting square of sheaves whose right-hand leg is a monomorphism and each of whose
sections lifts locally is cartesian. -/
theorem isPullback_of_mono_of_local_lift
    {P F G H : FppfSheaf B S hS}
    (fst : P ⟶ F) (snd : P ⟶ G) (f : F ⟶ H) (g : G ⟶ H)
    (hcomm : fst ≫ f = snd ≫ g) (hmono : Mono snd.hom)
    (hlift : ∀ (T : BigFppfOver B S hS) (x : F.obj.obj (op T)) (y : G.obj.obj (op T)),
      f.hom.app (op T) x = g.hom.app (op T) y →
      ∃ W ∈ BigFppfOver.topology B S hS T,
        ∀ ⦃T' : BigFppfOver B S hS⦄ (h : T' ⟶ T), W h →
          ∃ z : P.obj.obj (op T'),
            fst.hom.app (op T') z = F.obj.map h.op x ∧
              snd.hom.app (op T') z = G.obj.map h.op y) :
    IsPullback fst snd f g := by
  let J := BigFppfOver.topology B S hS
  let θ : P ⟶ pullback f g := pullback.lift fst snd hcomm
  have hθsnd : θ ≫ pullback.snd f g = snd := pullback.lift_snd _ _ _
  have hθfst : θ ≫ pullback.fst f g = fst := pullback.lift_fst _ _ _
  have hθsndP : θ.hom ≫ (pullback.snd f g).hom = snd.hom :=
    congrArg (fun t : P ⟶ G => t.hom) hθsnd
  have hθfstP : θ.hom ≫ (pullback.fst f g).hom = fst.hom :=
    congrArg (fun t : P ⟶ F => t.hom) hθfst
  have hinj : ∀ T : (BigFppfOver B S hS)ᵒᵖ, Function.Injective (θ.hom.app T) := by
    intro T z z' hz
    have hs : Mono (snd.hom.app T) := (NatTrans.mono_iff_mono_app snd.hom).1 hmono T
    refine (mono_iff_injective (snd.hom.app T)).1 hs ?_
    rw [← hθsndP]
    simp [hz]
  have hlocinj : Presheaf.IsLocallyInjective J θ.hom :=
    Presheaf.isLocallyInjective_of_injective J θ.hom hinj
  have hpbP : IsPullback (pullback.fst f g).hom (pullback.snd f g).hom f.hom g.hom :=
    (IsPullback.of_hasPullback f g).map (sheafToPresheaf J (Type (u + 1)))
  have hlocsurj : Presheaf.IsLocallySurjective J θ.hom := by
    refine ⟨fun {T} s => ?_⟩
    have hxy : f.hom.app (op T) ((pullback.fst f g).hom.app (op T) s) =
        g.hom.app (op T) ((pullback.snd f g).hom.app (op T) s) := by
      simpa using ConcreteCategory.congr_hom (congr_app hpbP.w (op T)) s
    obtain ⟨W, hW, hlifts⟩ := hlift T
      ((pullback.fst f g).hom.app (op T) s) ((pullback.snd f g).hom.app (op T) s) hxy
    refine J.superset_covering ?_ hW
    intro T' h hh
    obtain ⟨z, hz1, hz2⟩ := hlifts h hh
    refine ⟨z, ?_⟩
    refine Types.ext_of_isPullback (hpbP.app (op T')) ?_ ?_
    · rw [NatTrans.naturality_apply (pullback.fst f g).hom h.op s, ← hz1]
      simpa using ConcreteCategory.congr_hom (congr_app hθfstP (op T')) z
    · rw [NatTrans.naturality_apply (pullback.snd f g).hom h.op s, ← hz2]
      simpa using ConcreteCategory.congr_hom (congr_app hθsndP (op T')) z
  have hiso : IsIso θ := (Sheaf.isLocallyBijective_iff_isIso θ).1 ⟨hlocinj, hlocsurj⟩
  exact IsPullback.of_iso_pullback ⟨hcomm⟩ (@asIso _ _ _ _ θ hiso) hθfst hθsnd

/-! ### De-ulifting a subobject of a universe-lifted presheaf -/

/-- The subobject of a presheaf of `Type u` traced out by a morphism into its universe lift. -/
def downRange {C : Type*} [Category.{u} C]
    {F₀ : Cᵒᵖ ⥤ Type u} {Z : Cᵒᵖ ⥤ Type (u + 1)}
    (m : Z ⟶ F₀ ⋙ uliftFunctor.{u + 1}) : Subfunctor F₀ where
  obj T := {x | ∃ z, m.app T z = ULift.up x}
  map {T T'} h := by
    rintro x ⟨z, hz⟩
    refine ⟨Z.map h z, ?_⟩
    rw [NatTrans.naturality_apply m h z, hz]
    rfl

/-- A monomorphism into the universe lift of a presheaf of `Type u` identifies its source with
the universe lift of the subobject it traces out. -/
noncomputable def downRangeIso {C : Type*} [Category.{u} C]
    {F₀ : Cᵒᵖ ⥤ Type u} {Z : Cᵒᵖ ⥤ Type (u + 1)}
    (m : Z ⟶ F₀ ⋙ uliftFunctor.{u + 1}) (hm : Mono m) :
    Z ≅ (downRange m).toFunctor ⋙ uliftFunctor.{u + 1} := by
  have hinj (T : Cᵒᵖ) : Function.Injective (m.app T) :=
    (mono_iff_injective (m.app T)).1 ((NatTrans.mono_iff_mono_app m).1 hm T)
  let α : Z ⟶ (downRange m).toFunctor ⋙ uliftFunctor.{u + 1} :=
    { app T := ↾fun z => ULift.up ⟨(m.app T z).down, ⟨z, rfl⟩⟩
      naturality T T' h := by
        ext z
        apply ULift.ext
        apply Subtype.ext
        change (m.app T' (Z.map h z)).down = _
        rw [NatTrans.naturality_apply m h z]
        rfl }
  haveI happ : ∀ T : Cᵒᵖ, IsIso (α.app T) := by
    intro T
    rw [isIso_iff_bijective]
    refine ⟨fun z z' h => hinj T (ULift.ext (congrArg (fun y => (ULift.down y).1) h)), ?_⟩
    rintro ⟨⟨x, z, hz⟩⟩
    exact ⟨z, ULift.ext (Subtype.ext (congrArg ULift.down hz))⟩
  haveI : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- The identification `downRangeIso` followed by the universe lift of the inclusion of
`downRange m` is `m`. -/
theorem downRangeIso_hom_comp {C : Type*} [Category.{u} C]
    {F₀ : Cᵒᵖ ⥤ Type u} {Z : Cᵒᵖ ⥤ Type (u + 1)}
    (m : Z ⟶ F₀ ⋙ uliftFunctor.{u + 1}) (hm : Mono m) :
    (downRangeIso m hm).hom ≫
      Functor.whiskerRight (downRange m).ι uliftFunctor.{u + 1} = m := by
  ext T z
  rfl

/-- The subobject traced out by a monomorphism from a sheaf into the universe lift of a
presheaf of `Type u` is a sheaf. -/
theorem isSheaf_downRange {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    {F₀ : Cᵒᵖ ⥤ Type u} {Z : Cᵒᵖ ⥤ Type (u + 1)}
    (m : Z ⟶ F₀ ⋙ uliftFunctor.{u + 1}) (hm : Mono m)
    (hZ : Presheaf.IsSheaf J Z) :
    Presheaf.IsSheaf J (downRange m).toFunctor := by
  have h : Presheaf.IsSheaf J ((downRange m).toFunctor ⋙ uliftFunctor.{u + 1}) :=
    (Presheaf.isSheaf_of_iso_iff (downRangeIso m hm)).1 hZ
  rw [isSheaf_iff_isSheaf_of_type] at h ⊢
  rwa [← Presieve.isSheaf_comp_uliftFunctor_iff]

/-! ### The diagonal of a subobject of a formal algebraic space -/

/-- The identification of the sheafified Yoneda embedding, followed by the inclusion of sheaves
into presheaves, with the universe-lifted Yoneda embedding. -/
private noncomputable def sheafifiedYonedaCompIsoUliftYoneda :
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) ⋙
        sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)) ≅
      uliftYoneda.{u + 1} (C := BigFppfOver B S hS) :=
  letI : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  Functor.isoWhiskerRight
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS))
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))) ≪≫
    (BigFppfOver.topology B S hS).uliftYonedaCompSheafToPresheaf

/-- Representability relative to the sheafified Yoneda embedding passes to the underlying
presheaves. -/
private theorem relativelyRepresentable_forget
    {F G : FppfSheaf B S hS} (f : F ⟶ G)
    (hf : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable f) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) ⋙
        sheafToPresheaf (BigFppfOver.topology B S hS)
          (Type (u + 1))).relativelyRepresentable
      ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map f) := by
  intro U g
  let Pf := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  obtain ⟨g₀, hg₀⟩ := (show Pf.Full from inferInstance).map_surjective g
  obtain ⟨V, s, p, hp⟩ := hf g₀
  exact ⟨V, s, Pf.map p, hg₀ ▸ hp.map Pf⟩

/-- A morphism of fppf sheaves representable relative to the sheafified Yoneda embedding is
representable relative to the universe-lifted Yoneda embedding of presheaves. -/
theorem uliftYoneda_relativelyRepresentable_of_sheaf
    {F G : FppfSheaf B S hS} (m : F ⟶ G)
    (hm : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable m) :
    (uliftYoneda.{u + 1}).relativelyRepresentable m.hom :=
  (relative_of_natIso (sheafifiedYonedaCompIsoUliftYoneda B S hS)
    (⊤ : MorphismProperty (BigFppfOver B S hS)) _
    ⟨relativelyRepresentable_forget B S hS m hm, fun _ _ _ _ _ _ => trivial⟩).rep

/-- **Stacks 0AIP** read on presheaves: the diagonal of a formal algebraic space is
representable relative to the universe-lifted Yoneda embedding. -/
theorem uliftYoneda_relativelyRepresentable_diag {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) :
    (uliftYoneda.{u + 1}).relativelyRepresentable (diag X.obj) := by
  let J := BigFppfOver.topology B S hS
  let Pf := sheafToPresheaf J (Type (u + 1))
  have hdiagUL : (uliftYoneda.{u + 1}).relativelyRepresentable (Pf.map (diag X)) :=
    uliftYoneda_relativelyRepresentable_of_sheaf B S hS (diag X)
      (relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX)
  let eprod : Pf.obj (X ⨯ X) ≅ Pf.obj X ⨯ Pf.obj X := PreservesLimitPair.iso Pf X X
  have hdiagEq : Pf.map (diag X) ≫ eprod.hom = diag X.obj := by
    apply prod.hom_ext <;>
      simp only [diag, PreservesLimitPair.iso_hom, Category.assoc, prodComparison_fst,
        prodComparison_snd, ← Functor.map_comp, limit.lift_π, BinaryFan.mk_pt, BinaryFan.mk_fst,
        BinaryFan.mk_snd, CategoryTheory.Functor.map_id, eprod] <;>
      first | exact (prod.lift_fst _ _).symm | exact (prod.lift_snd _ _).symm
  have hdiagIso :
      (uliftYoneda.{u + 1}).relativelyRepresentable (Pf.map (diag X) ≫ eprod.hom) :=
    ((uliftYoneda.{u + 1}).relativelyRepresentable.cancel_right_of_respectsIso
      (Pf.map (diag X)) eprod.hom).2 hdiagUL
  rwa [hdiagEq] at hdiagIso

/-- A subobject of a presheaf with representable diagonal has representable diagonal. -/
theorem uliftYoneda_relativelyRepresentable_diag_of_mono {X R : FppfSheaf B S hS}
    (ι : R ⟶ X) (hmono : Mono ι.hom)
    (hX : (uliftYoneda.{u + 1}).relativelyRepresentable (diag X.obj)) :
    (uliftYoneda.{u + 1}).relativelyRepresentable (diag R.obj) := by
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  apply Functor.relativelyRepresentable.diag_of_map_from_obj
  intro a g a' g'
  obtain ⟨b, snd, fst, hpb⟩ :=
    Functor.relativelyRepresentable.of_diag hX (g ≫ ι.hom) (g' ≫ ι.hom)
  exact ⟨b, snd, fst, (isPullback_comp_mono_iff ι.hom).1 hpb⟩

/-- A chart of the base change `Rsp = R ×_X Xi` of a representable étale morphism `f` along a
monomorphism `ι` is étale over `R`. -/
theorem relative_etale_of_isPullback {X R Xi Rsp : FppfSheaf B S hS}
    (ι : R ⟶ X) (f : Xi ⟶ X) (k : Rsp ⟶ R) (jj : Rsp ⟶ Xi)
    (hsq : IsPullback k jj ι f)
    (hf : ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hfi)
    (U : BigFppfOver B S hS) (e : uliftYoneda.{u + 1}.obj U ≅ Rsp.obj)
    (hrep : (uliftYoneda.{u + 1}).relativelyRepresentable (e.hom ≫ k.hom)) :
    (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (e.hom ≫ k.hom) := by
  obtain ⟨hfi, het⟩ := hf
  let C := BigFppfOver B S hS
  let Y := uliftYoneda.{u + 1} (C := C)
  let P : MorphismProperty C :=
    MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  let : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  have hsqP : IsPullback k.hom jj.hom ι.hom f.hom :=
    hsq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  let : P.IsMultiplicative := {
    id_mem V := by
      change Etale (𝟙 V.left.obj)
      infer_instance
    comp_mem a b ha hb := by
      change Etale (a.left.hom ≫ b.left.hom)
      have : Etale a.left.hom := ha
      have : Etale b.left.hom := hb
      infer_instance }
  refine relative_of_representable_source_pullback_test Y P k.hom e hrep ?_
  intro T q V φ hφ
  have hpaste := (IsPullback.of_hasPullback q k.hom).paste_vert hsqP
  have hα : hpaste.isoPullback.hom ≫ pullback.fst (q ≫ ι.hom) f.hom =
      pullback.fst q k.hom := hpaste.isoPullback_hom_fst
  have hφ' : P.relative Y (φ ≫ hpaste.isoPullback.hom) :=
    MorphismProperty.RespectsIso.postcomp _ hpaste.isoPullback.hom φ hφ
  have hres : P.relative Y
      ((φ ≫ hpaste.isoPullback.hom) ≫ pullback.fst (q ≫ ι.hom) f.hom) :=
    het T (q ≫ ι.hom) V (φ ≫ hpaste.isoPullback.hom) hφ'
  rwa [Category.assoc, hα] at hres

/-! ### Reducedness of the charts of the glued subsheaf -/

/-- An algebraic space étale over a reduced object of the site is reduced. -/
theorem hasEtaleLocalPropertyULift_isReduced_of_isEtale_over_isReduced
    (T : BigFppfOver B S hS) (hT : IsReduced ((BigFppfOver.toScheme B S hS).obj T))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))
    (hF : Space.IsAlgebraicSpaceULift.{u + 1} B S hS F)
    (f : F ⟶ uliftYoneda.{u + 1}.obj T)
    (hf : Space.IsEtaleULift.{u + 1} B S hS f) :
    Space.HasEtaleLocalPropertyULift.{u + 1} B S hS F (fun V : Scheme.{u} => IsReduced V) := by
  obtain ⟨V, p, hps, hpe⟩ := hF.exists_atlas
  refine ⟨V, p, hps, hpe, ?_⟩
  let a : V ⟶ T := uliftYoneda.preimage (p ≫ f)
  have ha : uliftYoneda.{u + 1}.map a = p ≫ f := uliftYoneda.map_preimage _
  have hetale : Etale ((BigFppfOver.toScheme B S hS).map a) := by
    apply (hf V p hpe).property (𝟙 _) (𝟙 _) a
    simpa only [ha] using (IsPullback.of_id_fst (f := p ≫ f))
  exact isReduced_of_smooth ((BigFppfOver.toScheme B S hS).map a)

/-- A cartesian square stays cartesian when its top leg is factored through a monomorphism
into the lower-left corner. -/
private theorem isPullback_of_factorization_through_mono
    {C : Type*} [Category C] {P U V W X : C}
    {a : P ⟶ U} {b : P ⟶ V} {f : U ⟶ X} {g : V ⟶ X}
    (h : IsPullback a b f g) (j : W ⟶ U) [Mono j]
    (k : P ⟶ W) (hk : k ≫ j = a) : IsPullback k b (j ≫ f) g := by
  apply IsPullback.mk'
  · rw [← Category.assoc, hk, h.w]
  · intro T q r h₁ h₂
    apply h.hom_ext _ h₂
    rw [← hk, ← Category.assoc, h₁, Category.assoc]
  · intro T q r hqr
    have hw : (q ≫ j) ≫ f = r ≫ g := by
      simpa only [Category.assoc] using hqr
    refine ⟨h.lift (q ≫ j) r hw, ?_, h.lift_snd _ _ _⟩
    apply (cancel_mono j).1
    rw [Category.assoc, hk, h.lift_fst]

/-- **A reduced chart of `X` meeting a member `Y` of the atlas lands in the reduction of that
member.** Let `f : Y ⟶ X` be representable by algebraic spaces and étale, let `rY : Yred ⟶ Y`
be a reduction of `Y` and let `a : h_T ⟶ X` be a scheme-valued point with `T` reduced. Then
`h_T ×_X Y` maps to `Yred`, compatibly with its projection to `Y`, and the resulting square
over `rY ≫ f` is cartesian. -/
theorem exists_lift_reduced_chart_overlap {Y X : FppfSheaf B S hS} (f : Y ⟶ X)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (he : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hf)
    {Yred : FppfSheaf B S hS} {rY : Yred ⟶ Y} (hrY : IsReduction B S hS Y Yred rY)
    (T : BigFppfOver B S hS) (hT : IsReduced ((BigFppfOver.toScheme B S hS).obj T))
    (a : uliftYoneda.{u + 1}.obj T ⟶ X.obj) :
    ∃ k : pullback a f.hom ⟶ Yred.obj,
      k ≫ rY.hom = pullback.snd a f.hom ∧
      IsPullback k (pullback.fst a f.hom) (rY.hom ≫ f.hom) a := by
  let E : FppfSheaf B S hS := ⟨pullback a f.hom, (hf T a).isSheaf⟩
  have hE : Space.HasEtaleLocalPropertyULift.{u + 1} B S hS E.obj
      (fun V : Scheme.{u} => IsReduced V) :=
    hasEtaleLocalPropertyULift_isReduced_of_isEtale_over_isReduced B S hS T hT E.obj
      (hf T a) (pullback.fst a f.hom) (he T a)
  obtain ⟨k, hk, -⟩ := hrY.universal E (hf T a) hE ⟨pullback.snd a f.hom⟩
  have hk' : k.hom ≫ rY.hom = pullback.snd a f.hom :=
    congrArg (fun t : E ⟶ Y => t.hom) hk
  have : Mono rY.hom :=
    mono_of_isRepresentableThickeningULift B S hS hrY.isRepresentableThickening
  exact ⟨k.hom, hk', isPullback_of_factorization_through_mono
    (IsPullback.of_hasPullback a f.hom).flip rY.hom k.hom hk'⟩

/-- A section of a presheaf over an object of the site which is matched, over a reduced object,
by a section of a presheaf étale over it, lifts along the reduction of that object. -/
private theorem exists_lift_siteReductionMap_app
    {R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (T V : BigFppfOver B S hS) (hV : IsReduced ((BigFppfOver.toScheme B S hS).obj V))
    (p : uliftYoneda.{u + 1}.obj T ⟶ R)
    (hp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} p)
    (k : uliftYoneda.{u + 1}.obj V ⟶ R)
    (U : (BigFppfOver B S hS)ᵒᵖ)
    (x : (uliftYoneda.{u + 1}.obj T).obj U) (y : (uliftYoneda.{u + 1}.obj V).obj U)
    (hxy : p.app U x = k.app U y) :
    ∃ z, (uliftYoneda.{u + 1}.map (siteReductionMap B S hS T)).app U z = x := by
  let H := BigFppfOver.toScheme B S hS
  let r := siteReductionMap B S hS T
  let W := hp.rep.pullback k
  let q := hp.rep.snd k
  have hq : Etale (H.map q) := hp.property_snd k
  have : IsReduced (H.obj V) := hV
  have hW : IsReduced (H.obj W) := isReduced_of_smooth (H.map q)
  let b : W ⟶ T := uliftYoneda.preimage (hp.rep.fst k)
  have hb : uliftYoneda.{u + 1}.map b = hp.rep.fst k := uliftYoneda.map_preimage _
  obtain ⟨l, hl⟩ := exists_lift_siteReduction_of_isReduced B S hS r
    (isThickening_toScheme_map_siteReductionMap B S hS T) hW b
  have hpb := (hp.rep.isPullback k).map
    ((evaluation (BigFppfOver B S hS)ᵒᵖ (Type (u + 1))).obj U)
  obtain ⟨z, hz, -⟩ := Types.exists_of_isPullback hpb x y hxy
  refine ⟨(uliftYoneda.map l).app U z, ?_⟩
  have hmap : uliftYoneda.map l ≫ uliftYoneda.map r = hp.rep.fst k := by
    rw [← Functor.map_comp, hl, hb]
  change ((uliftYoneda.{u + 1}.map l ≫ uliftYoneda.{u + 1}.map r).app U) z = x
  rwa [hmap]

/-- **An object of the site étale over a sheafified union of images of reduced objects is
reduced.** -/
theorem isReduced_of_isEtale_into_sheafified_iSup_range
    {I : Type (u + 1)} (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))
    (Ti : I → BigFppfOver B S hS)
    (hTi : ∀ i, IsReduced ((BigFppfOver.toScheme B S hS).obj (Ti i)))
    (a : ∀ i, uliftYoneda.{u + 1}.obj (Ti i) ⟶ X)
    (T : BigFppfOver B S hS)
    (p : uliftYoneda.{u + 1}.obj T ⟶
      ((⨆ i, Subfunctor.range (a i)).sheafify (BigFppfOver.topology B S hS)).toFunctor)
    (hp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} p) :
    IsReduced ((BigFppfOver.toScheme B S hS).obj T) := by
  let J := BigFppfOver.topology B S hS
  let A : Subfunctor X := ⨆ i, Subfunctor.range (a i)
  let R := A.sheafify J
  let k (i : I) : uliftYoneda.{u + 1}.obj (Ti i) ⟶ R.toFunctor :=
    Subfunctor.lift (a i)
      ((le_iSup (fun i => Subfunctor.range (a i)) i).trans (A.le_sheafify J))
  refine isReduced_of_isLocallySurjective_siteReductionMap B S hS T ⟨fun {U} x => ?_⟩
  have hx : A.sieveOfSection (p.app (op U) x).val ∈ J U := (p.app (op U) x).property
  apply J.superset_covering ?_ hx
  intro V g hg
  change X.map g.op (p.app (op U) x).val ∈ A.obj (op V) at hg
  simp only [A, Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.range_obj] at hg
  obtain ⟨i, y, hy⟩ := hg
  have hw : p.app (op V) ((uliftYoneda.obj T).map g.op x) = (k i).app (op V) y :=
    Subtype.ext ((congrArg Subtype.val (p.naturality_apply g.op x)).trans hy.symm)
  exact exists_lift_siteReductionMap_app B S hS T (Ti i) (hTi i)
    p hp (k i) (op V) ((uliftYoneda.obj T).map g.op x) y hw

/-! ### Charts of a formal algebraic space through a prescribed point -/

/-- A scheme-valued point of `X` which factors through the member `Xi` of the atlas over a site
object admits, through any prescribed point of that object, an *affine* chart of the point which
is étale and still factors through `Xi`. -/
theorem exists_etale_affine_chart {X Xi : FppfSheaf B S hS} (fi : Xi ⟶ X)
    (hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS fi.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom) fi.hom hfi)
    (a : BigFppfOver B S hS) (g : uliftYoneda.{u + 1}.obj a ⟶ X.obj)
    (T : BigFppfOver B S hS) (b : T ⟶ a)
    (m : uliftYoneda.{u + 1}.obj T ⟶ Xi.obj)
    (hm : m ≫ fi.hom = uliftYoneda.{u + 1}.map b ≫ g)
    (y : T.left.obj) :
    ∃ (A : BigFppfOver B S hS) (c : A ⟶ a) (φ : uliftYoneda.{u + 1}.obj A ⟶ Xi.obj),
      IsAffine A.left.obj ∧ Etale c.left.hom ∧
        b.left.hom y ∈ Set.range c.left.hom ∧
        φ ≫ fi.hom = uliftYoneda.{u + 1}.map c ≫ g := by
  classical
  obtain ⟨Ua, t, hts, hte⟩ := (hfi a g).exists_atlas
  let ca : Ua ⟶ a := uliftYoneda.{u + 1}.preimage (t ≫ pullback.fst g fi.hom)
  have hcaeq : uliftYoneda.{u + 1}.map ca = t ≫ pullback.fst g fi.hom :=
    uliftYoneda.{u + 1}.map_preimage _
  have hcaP : (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) ca := by
    refine MorphismProperty.of_relative_map (F := uliftYoneda.{u + 1}) ?_
    rw [hcaeq]
    exact het a g Ua t hte
  have hca : Etale ca.left.hom := hcaP
  have hφa : (t ≫ pullback.snd g fi.hom) ≫ fi.hom = uliftYoneda.{u + 1}.map ca ≫ g := by
    rw [hcaeq, Category.assoc, Category.assoc, pullback.condition]
  let θ : uliftYoneda.{u + 1}.obj T ⟶ pullback g fi.hom :=
    pullback.lift (uliftYoneda.{u + 1}.map b) m hm.symm
  have hθf : θ ≫ pullback.fst g fi.hom = uliftYoneda.{u + 1}.map b :=
    pullback.lift_fst _ _ _
  have hprs : Surjective (hts.rep.snd θ).left.hom := hts.property_snd θ
  let ra : hts.rep.pullback θ ⟶ Ua := uliftYoneda.{u + 1}.preimage (hts.rep.fst θ)
  have hra : ra ≫ ca = hts.rep.snd θ ≫ b := by
    apply uliftYoneda.{u + 1}.map_injective
    rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, hcaeq,
      ← Category.assoc, (hts.rep.isPullback θ).w, Category.assoc, hθf]
  obtain ⟨y', hy'⟩ := hprs.surj y
  obtain ⟨-, ⟨O, hOaff, rfl⟩, hx₀, -⟩ :=
    (Scheme.isBasis_affineOpens Ua.left.obj).mem_nhds_iff.mp
      (isOpen_univ.mem_nhds (Set.mem_univ (ra.left.hom y')))
  have hUaS : Ua.left.obj.size < B.cutoff := Ua.left.property
  have hOsize : B.Contains (O : Scheme.{u}) :=
    lt_of_le_of_lt (Scheme.size_coe_opens_le Ua.left.obj O) hUaS
  let jO : B.obj hOsize ⟶ Ua.left := ⟨Scheme.Opens.ι O⟩
  let A : BigFppfOver B S hS :=
    Over.mk (Y := B.obj hOsize) (X := B.obj hS) (jO ≫ Ua.hom)
  let iA : A ⟶ Ua := Over.homMk jO
  have hiA : IsOpenImmersion iA.left.hom := by
    change IsOpenImmersion (Scheme.Opens.ι O)
    infer_instance
  have hAaff : IsAffine A.left.obj := hOaff
  refine ⟨A, iA ≫ ca, uliftYoneda.{u + 1}.map iA ≫ (t ≫ pullback.snd g fi.hom),
    hAaff, ?_, ?_, ?_⟩
  · change Etale (iA.left.hom ≫ ca.left.hom)
    infer_instance
  · refine ⟨⟨ra.left.hom y', hx₀⟩, ?_⟩
    rw [← hy']
    exact congrArg (fun z : hts.rep.pullback θ ⟶ a => z.left.hom y') hra
  · rw [Category.assoc, hφa, ← Category.assoc, ← Functor.map_comp]

/-- Every point of a site object carrying a scheme-valued point of `X` lies in the image of a
site object over which that point factors through one of the members of the atlas. -/
theorem exists_factorization_through_point
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)]
    {X : FppfSheaf B S hS} {I : Type (u + 1)} (Xi : I → FppfSheaf B S hS)
    (f : ∀ i, Xi i ⟶ X) (hcover : Sheaf.IsLocallySurjective (Sigma.desc f))
    (a : BigFppfOver B S hS) (g : uliftYoneda.{u + 1}.obj a ⟶ X.obj) (x : a.left.obj) :
    ∃ (i : I) (T : BigFppfOver B S hS) (b : T ⟶ a)
      (m : uliftYoneda.{u + 1}.obj T ⟶ (Xi i).obj) (y : T.left.obj),
      m ≫ (f i).hom = uliftYoneda.{u + 1}.map b ≫ g ∧ b.left.hom y = x := by
  classical
  have hmem := family_imageSieve_mem (BigFppfOver.topology B S hS) Xi X f hcover a
    (uliftYonedaEquiv g)
  rw [GrothendieckTopology.mem_over_iff] at hmem
  obtain ⟨E, hE, hER⟩ := Space.exists_covering_refining_sieve B hmem
  have hEF := B.isFppfCovering_of_isCovering hE
  rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
    PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
    Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hEF
  obtain ⟨j, y, hy⟩ := hEF.1 x
  let T : BigFppfOver B S hS := Over.mk (E.f j ≫ a.hom)
  let b : T ⟶ a := Over.homMk (E.f j)
  have hb := (Sieve.overEquiv_iff _ _).mp (hER _ _ ⟨j⟩)
  change (⨆ i, Presheaf.imageSieve (f i).hom (uliftYonedaEquiv g)) b at hb
  simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hb
  obtain ⟨-, ⟨i, rfl⟩, z, hz⟩ := hb
  refine ⟨i, T, b, uliftYonedaEquiv.symm z, y, ?_, hy⟩
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  exact hz.trans (uliftYonedaEquiv_naturality.{u + 1} g b.op)

/-- Over a chart of `a` whose composite into `X` factors through the member `Xi` of the atlas,
the base change of `ι` is represented by a thickening of objects of the site. -/
theorem exists_thickening_chart {X R Xi Rsp : FppfSheaf B S hS}
    (ι : R ⟶ X) (fi : Xi ⟶ X) (ki : Rsp ⟶ R) (jji : Rsp ⟶ Xi)
    (hsq : IsPullback ki jji ι fi)
    (hjj : Space.IsRepresentableThickeningULift.{u + 1} B S hS jji.hom)
    {a : BigFppfOver B S hS} (g : uliftYoneda.{u + 1}.obj a ⟶ X.obj)
    (A : BigFppfOver B S hS) (c : A ⟶ a) (φ : uliftYoneda.{u + 1}.obj A ⟶ Xi.obj)
    (hφ : φ ≫ fi.hom = uliftYoneda.{u + 1}.map c ≫ g) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ A) (v : uliftYoneda.{u + 1}.obj V ⟶ R.obj),
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map p) ∧
      IsPullback v (uliftYoneda.{u + 1}.map p) ι.hom
        (uliftYoneda.{u + 1}.map c ≫ g) := by
  have hsqP : IsPullback ki.hom jji.hom ι.hom fi.hom :=
    hsq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  have hbigP := (hjj.rep.isPullback φ).paste_horiz hsqP
  rw [hφ] at hbigP
  exact ⟨hjj.rep.pullback φ, hjj.rep.snd φ, hjj.rep.fst φ ≫ ki.hom,
    hjj.property_snd φ, hbigP⟩

/-! ### The étale atlas underlying the general case -/

/-- Let `{Xi i ⟶ X}` be a jointly surjective family of morphisms representable by algebraic
spaces and étale, over each member of which the base change of `ι : R ⟶ X` is a representable
thickening. For a scheme-valued point `g : h_a ⟶ X` there is a single object `W` of the site,
surjective and étale over `a`, over which the base change of `ι` is represented by an object `V`
of the site whose morphism to `W` is a thickening. -/
theorem exists_etale_atlas_of_pullback_thickening
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)]
    {X R : FppfSheaf B S hS} (ι : R ⟶ X) {I : Type (u + 1)}
    (Xi Rsp : I → FppfSheaf B S hS)
    (f : ∀ i, Xi i ⟶ X) (k : ∀ i, Rsp i ⟶ R) (jj : ∀ i, Rsp i ⟶ Xi i)
    (hsq : ∀ i, IsPullback (k i) (jj i) ι (f i))
    (hf : ∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi)
    (hcover : Sheaf.IsLocallySurjective (Sigma.desc f))
    (hjj : ∀ i, Space.IsRepresentableThickeningULift.{u + 1} B S hS (jj i).hom)
    (a : BigFppfOver B S hS) (g : uliftYoneda.{u + 1}.obj a ⟶ X.obj) :
    ∃ (W V : BigFppfOver B S hS) (w : W ⟶ a) (p : V ⟶ W)
      (v : uliftYoneda.{u + 1}.obj V ⟶ R.obj),
      Surjective ((BigFppfOver.toScheme B S hS).map w) ∧
      Etale ((BigFppfOver.toScheme B S hS).map w) ∧
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map p) ∧
      IsPullback v (uliftYoneda.{u + 1}.map p) ι.hom
        (uliftYoneda.{u + 1}.map w ≫ g) := by
  classical
  have hresp : MorphismProperty.RespectsIso
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) :=
    isThickening_isStableUnderBaseChange.respectsIso
  have hchart : ∀ x : a.left.obj, ∃ (i : I) (A : BigFppfOver B S hS)
      (c : A ⟶ a) (φ : uliftYoneda.{u + 1}.obj A ⟶ (Xi i).obj),
      IsAffine A.left.obj ∧ Etale c.left.hom ∧ x ∈ Set.range c.left.hom ∧
        φ ≫ (f i).hom = uliftYoneda.{u + 1}.map c ≫ g := by
    intro x
    obtain ⟨i, T, b, m, y, hm, hy⟩ :=
      exists_factorization_through_point B S hS Xi f hcover a g x
    obtain ⟨hfi, het⟩ := hf i
    obtain ⟨A, c, φ, hAff, hcet, hcmem, hcfac⟩ :=
      exists_etale_affine_chart B S hS (f i) hfi het a g T b m hm y
    exact ⟨i, A, c, φ, hAff, hcet, hy ▸ hcmem, hcfac⟩
  choose ix Ax cx φx hAaff hcet hcmem hcfac using hchart
  have hAsize : ∀ x, (Ax x).left.obj.size ≤ a.left.obj.size := by
    intro x
    have : IsAffine (Ax x).left.obj := hAaff x
    have : Etale (cx x).left.hom := hcet x
    exact Scheme.size_le_of_locallyOfFiniteType (cx x).left.hom
  obtain ⟨W, kk, q, hkq, hkOI, hkcov, hkdisj⟩ :=
    exists_map_from_coproduct B S hS
      (⟨uliftYoneda.{u + 1}.obj a,
        (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS a).isSheaf⟩ :
        FppfSheaf B S hS)
      Ax (fun x => uliftYoneda.{u + 1}.map (cx x))
      (contains_coproduct_of_size_le B S hS Ax hAsize)
  let w : W ⟶ a := uliftYoneda.{u + 1}.preimage q
  have hkw (x) : kk x ≫ w = cx x :=
    uliftYoneda.{u + 1}.map_injective (by rw [Functor.map_comp, Functor.map_preimage, hkq x])
  have hkwh : ∀ x, (kk x).left.hom ≫ w.left.hom = (cx x).left.hom := fun x =>
    congrArg (fun z : Ax x ⟶ a => z.left.hom) (hkw x)
  let DW : W.left.obj.OpenCover :=
    { I₀ := a.left.obj
      X x := (Ax x).left.obj
      f x := (kk x).left.hom
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hkcov, hkOI⟩ }
  have hwsurj : Surjective w.left.hom := by
    refine ⟨fun z => ?_⟩
    obtain ⟨z', hz'⟩ := hcmem z
    exact ⟨(kk z).left.hom z',
      (congrArg (fun t : (Ax z).left.obj ⟶ a.left.obj => t z') (hkwh z)).trans hz'⟩
  have hwet : Etale w.left.hom := by
    have : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
    refine IsZariskiLocalAtSource.of_openCover (P := @Etale.{u}) DW (fun x => ?_)
    change Etale ((kk x).left.hom ≫ w.left.hom)
    rw [hkwh x]
    exact hcet x
  have hthchart : ∀ x : a.left.obj, ∃ (Vx : BigFppfOver B S hS)
      (px : Vx ⟶ Ax x) (vx : uliftYoneda.{u + 1}.obj Vx ⟶ R.obj),
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map px) ∧
      IsPullback vx (uliftYoneda.{u + 1}.map px) ι.hom
        (uliftYoneda.{u + 1}.map (cx x) ≫ g) := fun x =>
    exists_thickening_chart B S hS ι (f (ix x)) (k (ix x)) (jj (ix x)) (hsq (ix x))
      (hjj (ix x)) g (Ax x) (cx x) (φx x) (hcfac x)
  choose Vx px vx hth hpbx using hthchart
  have hVsize : ∀ x, (Vx x).left.obj.size ≤ a.left.obj.size := by
    intro x
    have : IsClosedImmersion (px x).left.hom := (hth x).1
    have : IsAffine (Ax x).left.obj := hAaff x
    have : Mono (px x).left.hom := inferInstance
    exact (Scheme.size_le_of_mono_quasiCompact (px x).left.hom).trans (hAsize x)
  obtain ⟨V, kv, v, hvfac, hkvOI, hkvcov, hkvdisj⟩ :=
    exists_map_from_coproduct B S hS R Vx vx
      (contains_coproduct_of_size_le B S hS Vx hVsize)
  obtain ⟨pq, hpq⟩ := exists_amalgamation_of_disjoint_openCover B S hS
    (⟨uliftYoneda.{u + 1}.obj W,
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS W).isSheaf⟩ : FppfSheaf B S hS)
    Vx kv hkvOI hkvcov hkvdisj (fun x => uliftYoneda.{u + 1}.map (px x ≫ kk x))
  let p : V ⟶ W := uliftYoneda.{u + 1}.preimage pq
  have hpsq (x) : kv x ≫ p = px x ≫ kk x :=
    uliftYoneda.{u + 1}.map_injective (by rw [Functor.map_comp, Functor.map_preimage, hpq x])
  have hpsqh : ∀ x, (kv x).left.hom ≫ p.left.hom =
      (px x).left.hom ≫ (kk x).left.hom := fun x =>
    congrArg (fun z : Vx x ⟶ W => z.left.hom) (hpsq x)
  have hthsq : ∀ x, IsPullback (px x).left.hom (kv x).left.hom
      (kk x).left.hom p.left.hom := by
    intro x
    have hoi1 : IsOpenImmersion (kv x).left.hom := hkvOI x
    have hoi2 : IsOpenImmersion (kk x).left.hom := hkOI x
    refine AlgebraicGeometry.IsOpenImmersion.isPullback _ _ _ _ (hpsqh x) ?_
    refine TopologicalSpace.Opens.ext (Set.eq_of_subset_of_subset ?_ ?_)
    · intro z hz
      obtain ⟨yy, z', hz'⟩ := hkvcov z
      have hpz : p.left.hom z = (kk yy).left.hom ((px yy).left.hom z') := by
        rw [← hz']
        exact congrArg (fun t : (Vx yy).left.obj ⟶ W.left.obj => t z') (hpsqh yy)
      obtain ⟨t, ht⟩ := hz
      have hyy : yy = x := by
        by_contra hne
        exact hkdisj yy x hne ((px yy).left.hom z') t (ht.trans hpz).symm
      subst hyy
      exact ⟨z', hz'⟩
    · intro z hz
      obtain ⟨z', hz'⟩ := hz
      refine ⟨(px x).left.hom z', ?_⟩
      rw [← hz']
      exact (congrArg (fun t : (Vx x).left.obj ⟶ W.left.obj => t z') (hpsqh x)).symm
  have hwthick : Stacks.Thickenings.IsThickening p.left.hom := by
    have hlat := isThickening_isLocalAtTarget_fppf.{u}
    have hRmem : Presieve.ofArrows (fun x : a.left.obj => (Ax x).left.obj)
        (fun x => (kk x).left.hom) ∈ Scheme.fppfPrecoverage W.left.obj := by
      rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
      refine ⟨hkcov, fun x => ?_⟩
      have := hkOI x
      exact ⟨inferInstance, inferInstance⟩
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hRmem ?_
    intro U gg _ hg
    obtain ⟨x⟩ := hg
    rw [← (hthsq x).flip.isoPullback_inv_snd]
    exact MorphismProperty.RespectsIso.precomp _ (hthsq x).flip.isoPullback.inv
      (px x).left.hom (hth x)
  have hpmono : Mono p := by
    have : IsClosedImmersion p.left.hom := hwthick.1
    have : Mono p.left := B.inclusion.mono_of_mono_map (inferInstance : Mono p.left.hom)
    exact Over.mono_of_mono_left _
  have hcommP : v ≫ ι.hom = uliftYoneda.{u + 1}.map p ≫
      (uliftYoneda.{u + 1}.map w ≫ g) := by
    refine uliftYoneda_hom_ext_of_openCover B S hS X Vx kv hkvOI hkvcov _ _ (fun x => ?_)
    rw [← Category.assoc, hvfac x, ← Category.assoc, ← Functor.map_comp, hpsq x,
      Functor.map_comp, Category.assoc, ← Category.assoc
        (uliftYoneda.{u + 1}.map (kk x)), ← Functor.map_comp, hkw x]
    exact (hpbx x).w
  have hbigSheaf : IsPullback
      (⟨v⟩ : (⟨uliftYoneda.{u + 1}.obj V,
          (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS V).isSheaf⟩ :
          FppfSheaf B S hS) ⟶ R)
      (⟨uliftYoneda.{u + 1}.map p⟩ : _ ⟶ (⟨uliftYoneda.{u + 1}.obj W,
          (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS W).isSheaf⟩ :
          FppfSheaf B S hS))
      ι (⟨uliftYoneda.{u + 1}.map w ≫ g⟩) := by
    refine isPullback_of_mono_of_local_lift B S hS _ _ _ _
      (Sheaf.hom_ext hcommP) (uliftYoneda_map_mono B S hS p hpmono) ?_
    intro T xel yel hxy
    obtain ⟨xr, rfl⟩ := uliftYonedaEquiv.{u + 1}.surjective xel
    obtain ⟨yw, rfl⟩ := uliftYonedaEquiv.{u + 1}.surjective yel
    have hxy' : xr ≫ ι.hom = yw ≫ (uliftYoneda.{u + 1}.map w ≫ g) :=
      uliftYonedaEquiv.{u + 1}.injective hxy
    let β : T ⟶ W := uliftYoneda.{u + 1}.preimage yw
    have hβ : uliftYoneda.{u + 1}.map β = yw := uliftYoneda.{u + 1}.map_preimage _
    let Tx (x : a.left.obj) : BigFppfOver B S hS := pullback (kk x) β
    let ax (x : a.left.obj) : Tx x ⟶ Ax x := pullback.fst (kk x) β
    let bx (x : a.left.obj) : Tx x ⟶ T := pullback.snd (kk x) β
    have hpbA (x : a.left.obj) := (IsPullback.of_hasPullback (kk x) β).map
      (BigFppfOver.toScheme B S hS)
    have hbxOI : ∀ x, IsOpenImmersion (bx x).left.hom := fun x =>
      MorphismProperty.of_isPullback (hpbA x) (hkOI x)
    have hbxcov : ∀ z : T.left.obj, ∃ x, z ∈ Set.range (bx x).left.hom := by
      intro z
      obtain ⟨x, y₀, hy₀⟩ := Scheme.Cover.exists_eq (DW.pullback₂ β.left.hom) z
      exact ⟨x, (hpbA x).isoPullback.inv y₀,
        (congrArg (fun t : pullback (kk x).left.hom β.left.hom ⟶ T.left.obj => t y₀)
          (hpbA x).isoPullback_inv_snd).trans hy₀⟩
    refine ⟨Sieve.ofArrows Tx bx, fppf_ofArrows_mem B S hS Tx bx
      (fun x => by have := hbxOI x; infer_instance)
      (fun x => by have := hbxOI x; infer_instance) hbxcov, ?_⟩
    intro T' h hh
    obtain ⟨T'', e, -, ⟨x⟩, hfac⟩ := hh
    have hcond : ax x ≫ kk x = bx x ≫ β := pullback.condition
    have hθcomm : (uliftYoneda.{u + 1}.map (bx x) ≫ xr) ≫ ι.hom =
        uliftYoneda.{u + 1}.map (ax x) ≫ (uliftYoneda.{u + 1}.map (cx x) ≫ g) := by
      rw [Category.assoc, hxy', ← hβ, ← Category.assoc, ← Functor.map_comp,
        ← hcond, Functor.map_comp, Category.assoc, ← Category.assoc
          (uliftYoneda.{u + 1}.map (kk x)), ← Functor.map_comp, hkw x]
    obtain ⟨zz, hzz1, hzz2⟩ : ∃ zz : uliftYoneda.{u + 1}.obj (Tx x) ⟶
        uliftYoneda.{u + 1}.obj (Vx x),
        zz ≫ vx x = uliftYoneda.{u + 1}.map (bx x) ≫ xr ∧
        zz ≫ uliftYoneda.{u + 1}.map (px x) = uliftYoneda.{u + 1}.map (ax x) :=
      ⟨(hpbx x).lift _ _ hθcomm, (hpbx x).lift_fst _ _ _, (hpbx x).lift_snd _ _ _⟩
    refine ⟨uliftYonedaEquiv (uliftYoneda.{u + 1}.map e ≫ zz ≫
      uliftYoneda.{u + 1}.map (kv x)), ?_, ?_⟩
    · refine ((uliftYonedaEquiv_comp (uliftYoneda.{u + 1}.map e ≫ zz ≫
        uliftYoneda.{u + 1}.map (kv x)) v).symm.trans
          (congrArg uliftYonedaEquiv ?_)).trans
            (uliftYonedaEquiv_naturality.{u + 1} xr h.op).symm
      rw [Category.assoc, Category.assoc, hvfac x, hzz1, ← Category.assoc,
        ← Functor.map_comp, hfac]
      rfl
    · refine ((uliftYonedaEquiv_comp (uliftYoneda.{u + 1}.map e ≫ zz ≫
        uliftYoneda.{u + 1}.map (kv x)) (uliftYoneda.{u + 1}.map p)).symm.trans
          (congrArg uliftYonedaEquiv ?_)).trans
            (uliftYonedaEquiv_naturality.{u + 1} yw h.op).symm
      rw [Category.assoc, Category.assoc, ← Functor.map_comp, hpsq x,
        Functor.map_comp, ← Category.assoc zz, hzz2, ← Functor.map_comp, hcond,
        Functor.map_comp, ← Category.assoc, ← Functor.map_comp, hfac, hβ]
      rfl
  exact ⟨W, V, w, p, v, hwsurj, hwet, hwthick,
    hbigSheaf.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))⟩

/-! ### Descent of the representable-thickening property -/

/-- **Descent of the representable-thickening property along a jointly surjective representable
étale family.** Let `ι : R ⟶ X` be a monomorphism of fppf sheaves and let `{Xi ⟶ X}` be a
jointly surjective family of morphisms representable by algebraic spaces and étale, over each
member of which the base change of `ι` is a representable thickening. Then `ι` is a
representable thickening. -/
theorem isRepresentableThickeningULift_of_isPullback_etale_cover
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)]
    {X R : FppfSheaf B S hS} (ι : R ⟶ X) (hmono : Mono ι.hom) {I : Type (u + 1)}
    (Xi Rsp : I → FppfSheaf B S hS)
    (f : ∀ i, Xi i ⟶ X) (k : ∀ i, Rsp i ⟶ R) (jj : ∀ i, Rsp i ⟶ Xi i)
    (hsq : ∀ i, IsPullback (k i) (jj i) ι (f i))
    (hf : ∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi)
    (hcover : Sheaf.IsLocallySurjective (Sigma.desc f))
    (hjj : ∀ i, Space.IsRepresentableThickeningULift.{u + 1} B S hS (jj i).hom) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS ι.hom := by
  classical
  let J := BigFppfOver.topology B S hS
  let Q : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  let Wf : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
    (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
      uliftFunctor.{u + 1}
  have : MorphismProperty.RespectsIso
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) :=
    isThickening_isStableUnderBaseChange.respectsIso
  have : Q.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  have : MorphismProperty.RespectsIso (@LocallyQuasiFinite.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso (@LocallyOfFiniteType.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite :
        MorphismProperty Scheme.{u}) :=
    MorphismProperty.RespectsIso.inf _ _
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}) :=
    MorphismProperty.RespectsIso.inf _ _
  have : (show MorphismProperty Scheme.{u} from
      @Stacks.Thickenings.IsThickening).IsLocalAtTarget Scheme.fppfPrecoverage :=
    isThickening_isLocalAtTarget_fppf.{u}
  apply MorphismProperty.relative.of_exists
  intro a g
  let m := pullback.snd ι.hom g
  have hZP : IsPullback (pullback.fst ι.hom g) m ι.hom g := IsPullback.of_hasPullback ι.hom g
  have hmm : Mono m :=
    MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms _) hZP hmono
  have hZsheaf : Presheaf.IsSheaf J (pullback ι.hom g) :=
    Presheaf.isSheaf_pullback _ ι.hom g R.property
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS a).isSheaf X.property
  let G₀ := (downRange (F₀ := yoneda.obj a) m).toFunctor
  let f₀ : G₀ ⟶ yoneda.obj a := (downRange (F₀ := yoneda.obj a) m).ι
  let eZ : (pullback ι.hom g) ≅ G₀ ⋙ uliftFunctor.{u + 1} :=
    downRangeIso (F₀ := yoneda.obj a) m hmm
  have heZ' : eZ.hom ≫ Functor.whiskerRight f₀ uliftFunctor.{u + 1} = m :=
    downRangeIso_hom_comp (F₀ := yoneda.obj a) m hmm
  obtain ⟨W, V, w, p, v, hwsurj, hwet, hpthick, hvpb⟩ :=
    exists_etale_atlas_of_pullback_thickening B S hS ι Xi Rsp f k jj hsq hf hcover hjj a g
  let v' : uliftYoneda.{u + 1}.obj V ⟶ pullback ι.hom g :=
    hZP.lift v (uliftYoneda.{u + 1}.map p ≫ uliftYoneda.{u + 1}.map w)
      (by rw [Category.assoc]; exact hvpb.w)
  have hv'fst : v' ≫ pullback.fst ι.hom g = v := hZP.lift_fst _ _ _
  have hv'snd : v' ≫ m = uliftYoneda.{u + 1}.map p ≫ uliftYoneda.{u + 1}.map w :=
    hZP.lift_snd _ _ _
  have hv' : IsPullback v' (uliftYoneda.{u + 1}.map p) m (uliftYoneda.{u + 1}.map w) :=
    IsPullback.of_right (by rwa [hv'fst]) hv'snd hZP
  have hbig : IsPullback (v' ≫ eZ.hom) (uliftYoneda.{u + 1}.map p)
      (Functor.whiskerRight f₀ uliftFunctor.{u + 1}) (uliftYoneda.{u + 1}.map w) :=
    hv'.of_iso (Iso.refl _) eZ (Iso.refl _) (Iso.refl _)
      (Category.id_comp (v' ≫ eZ.hom)).symm
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id m).trans heZ'.symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨i₀, hi₀⟩ := Wf.map_surjective
    (show Wf.obj (yoneda.obj V) ⟶ Wf.obj G₀ from v' ≫ eZ.hom)
  have hsmall : IsPullback i₀ (yoneda.map p) f₀ (yoneda.map w) := by
    have hb : IsPullback (Wf.map i₀) (Wf.map (yoneda.map p)) (Wf.map f₀)
        (Wf.map (yoneda.map w)) := by
      rwa [hi₀]
    refine hb.of_map Wf ?_
    apply (show Wf.Faithful from inferInstance).map_injective
    simpa only [Functor.map_comp] using hb.w
  have hqsurj :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@Surjective.{u} : MorphismProperty Scheme.{u}) w).2 hwsurj
  have hqetale :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@Etale.{u} : MorphismProperty Scheme.{u}) w).2 hwet
  have hchartQ : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map p) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) p).2 hpthick
  have hbase : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f₀ (yoneda.map w)) := by
    rw [← hsmall.isoPullback_inv_snd]
    exact MorphismProperty.RespectsIso.precomp _ hsmall.isoPullback.inv _ hchartQ
  have hrep₀ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f₀ :=
    Space.presheaf_of_surjectiveEtaleChart
      (Space.isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_locallyQuasiFinite_inf_lft
        B S hS)
      (isSheaf_downRange J (F₀ := yoneda.obj a) m hmm hZsheaf)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS a).isSheaf hqsurj hqetale
      (presheaf_mono_of_le B S hS
        (fun _ h =>
          isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_of_isThickening h) hbase)
  have h03KD : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f₀ :=
    Space.presheaf_of_isLocallySurjective_pullback B S hS
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) f₀ (yoneda.map w)
      hrep₀.rep
      (AlgebraicGeometry.isLocallySurjective_of_surjective_etale B S hS (yoneda.map w)
        hqsurj hqetale)
      hbase
  have hmQ : Q.relative uliftYoneda.{u + 1} m := by
    have : (Q.relative uliftYoneda.{u + 1}).RespectsIso :=
      (MorphismProperty.relative_isStableUnderBaseChange
        (F := uliftYoneda.{u + 1}) Q).respectsIso
    have h1 : Q.relative uliftYoneda.{u + 1}
        (Functor.whiskerRight f₀ uliftFunctor.{u + 1}) :=
      Space.relative_ulift_of_presheaf Q f₀ h03KD
    have h2 : Q.relative uliftYoneda.{u + 1}
        (eZ.hom ≫ Functor.whiskerRight f₀ uliftFunctor.{u + 1}) :=
      MorphismProperty.RespectsIso.precomp _ eZ.hom _ h1
    rwa [heZ'] at h2
  refine ⟨hmQ.rep.pullback (𝟙 (uliftYoneda.{u + 1}.obj a)),
    hmQ.rep.fst (𝟙 _) ≫ pullback.fst ι.hom g, hmQ.rep.snd (𝟙 _), ?_,
    hmQ.property_snd (𝟙 _)⟩
  have hp := (hmQ.rep.isPullback (𝟙 (uliftYoneda.{u + 1}.obj a))).paste_horiz hZP
  rwa [Category.id_comp] at hp

/-! ### The glued reduction is an algebraic space -/

/-- Let `ι : R ⟶ X` be a monomorphism of fppf sheaves into a formal algebraic space which is a
representable thickening, and let `R` be covered by the base changes `Rsp i` along `ι` of a
family `{Xi i ⟶ X}` of morphisms representable by algebraic spaces and étale, each `Rsp i`
represented by an affine object `Ui i` of the site. Then `R` is an algebraic space. -/
theorem isAlgebraicSpaceULift_of_reduced_etale_cover
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)]
    {X R : FppfSheaf B S hS} (ι : R ⟶ X) (hmono : Mono ι.hom)
    (hX : IsFormalAlgebraicSpace B S hS X) {I : Type (u + 1)}
    (Xi Rsp : I → FppfSheaf B S hS) (Ui : I → BigFppfOver B S hS)
    (hUi : ∀ i, IsAffine (Ui i).left.obj)
    (eRsp : ∀ i, uliftYoneda.{u + 1}.obj (Ui i) ≅ (Rsp i).obj)
    (f : ∀ i, Xi i ⟶ X) (k : ∀ i, Rsp i ⟶ R) (jj : ∀ i, Rsp i ⟶ Xi i)
    (hsq : ∀ i, IsPullback (k i) (jj i) ι (f i))
    (hf : ∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi)
    (hcoverR : Sheaf.IsLocallySurjective (Sigma.desc k))
    (hι : Space.IsRepresentableThickeningULift.{u + 1} B S hS ι.hom) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS R.obj := by
  classical
  let J := BigFppfOver.topology B S hS
  let C := BigFppfOver B S hS
  let Y := uliftYoneda.{u + 1} (C := C)
  let : HasBinaryProducts C := Over.ConstructProducts.over_binaryProduct_of_pullback
  have hdiagR := uliftYoneda_relativelyRepresentable_diag_of_mono B S hS ι hmono
    (uliftYoneda_relativelyRepresentable_diag B S hS hX)
  refine ⟨R.property, hdiagR, ?_⟩
  let P : MorphismProperty C :=
    MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  let : MorphismProperty.IsStableUnderBaseChange (@Etale : MorphismProperty Scheme.{u}) :=
    Etale.etale_isStableUnderBaseChange
  let : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  let gi (i : I) : Y.obj (Ui i) ⟶ R.obj := (eRsp i).hom ≫ (k i).hom
  have hgi (i : I) : P.relative Y (gi i) :=
    relative_etale_of_isPullback B S hS ι (f i) (k i) (jj i) (hsq i) (hf i)
      (Ui i) (eRsp i) (Functor.relativelyRepresentable.of_diag hdiagR (gi i))
  have he (i : I) : P.relative Y (k i).hom :=
    ((P.relative Y).cancel_left_of_respectsIso (eRsp i).hom (k i).hom).mp (hgi i)
  obtain ⟨U, -, hU, -, ⟨eU⟩, -, t, ht, -⟩ := hX.1
  let t' : Y.obj U ⟶ X.obj := eU.inv ≫ t.hom
  have ht' : Presheaf.IsLocallySurjective J t' := by
    have : Sheaf.IsLocallySurjective t := (Sheaf.isLocallySurjective_iff_epi t).mpr ht
    dsimp only [t']
    infer_instance
  have hιrep : Y.relativelyRepresentable ι.hom := hι.rep
  let UR : C := hιrep.pullback t'
  let tR : Y.obj UR ⟶ R.obj := hιrep.fst t'
  have htR : Presheaf.IsLocallySurjective J tR :=
    Presheaf.isLocallySurjective_of_isPullback J (hιrep.isPullback t')
  have hsize (i : I) : (Ui i).left.obj.size ≤ UR.left.obj.size := by
    have : IsAffine (Ui i).left.obj := hUi i
    exact affineChart_size_le B S hS UR (Ui i) (eRsp i).symm tR htR (k i) (he i)
  let Wi (i : I) : C := (hgi i).rep.pullback tR
  let pi (i : I) : Wi i ⟶ UR := (hgi i).rep.snd tR
  let ri (i : I) : Wi i ⟶ Ui i := Y.preimage ((hgi i).rep.fst tR)
  have hpi (i : I) : Etale (pi i).left.hom := (hgi i).property_snd tR
  have hfac (i : I) : Y.map (ri i) ≫ gi i = Y.map (pi i) ≫ tR := by
    rw [Y.map_preimage]
    exact ((hgi i).rep.isPullback tR).w
  have hpoint : ∀ x : UR.left.obj, ∃ i, x ∈ Set.range (pi i).left.hom := by
    intro x
    obtain ⟨i, T, b, m, y, hm, hy⟩ :=
      exists_factorization_through_point B S hS Rsp k hcoverR UR tR x
    have hw : (m ≫ (eRsp i).inv) ≫ gi i = Y.map b ≫ tR := by
      simpa only [gi, Category.assoc, Iso.inv_hom_id_assoc] using hm
    let a : T ⟶ Wi i := Y.preimage
      (((hgi i).rep.isPullback tR).lift (m ≫ (eRsp i).inv) (Y.map b) hw)
    have hab : a ≫ pi i = b := Y.map_injective (by
      rw [Y.map_comp, Y.map_preimage]
      exact ((hgi i).rep.isPullback tR).lift_snd _ _ _)
    refine ⟨i, a.left.hom y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← show (a ≫ pi i).left.hom =
      a.left.hom ≫ (pi i).left.hom from rfl, hab]
    exact hy
  choose idx hidx using hpoint
  obtain ⟨W, kk, q, hkq, hk, hkcov, -⟩ :=
    exists_map_from_coproduct B S hS R (fun x => Ui (idx x))
      (fun x => gi (idx x))
      (contains_coproduct_of_size_le B S hS (fun x => Ui (idx x)) fun x => hsize (idx x))
  have hqrep : Y.relativelyRepresentable q :=
    Functor.relativelyRepresentable.of_diag hdiagR q
  have hqet : P.relative Y q := etale_of_openCover B S hS _ kk hk hkcov q hqrep
    (fun x => (hkq x).symm ▸ hgi (idx x))
  have hqsurj : Presheaf.IsLocallySurjective J q := by
    let V := fun x : UR.left.obj => Wi (idx x)
    let pp := fun x : UR.left.obj => pi (idx x)
    have hmem : Sieve.ofArrows V pp ∈ J UR := fppf_ofArrows_mem B S hS V pp
      (fun x => by have := hpi (idx x); infer_instance)
      (fun x => by have := hpi (idx x); infer_instance)
      (fun x => ⟨x, hidx x⟩)
    have hsmall : Presheaf.IsLocallySurjective J
        (Sigma.desc (fun x : UR.left.obj => Y.map (pp x))) :=
      (GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
        J pp).mp hmem
    let aa : ∐ (fun x : UR.left.obj => Y.obj (V x)) ⟶ Y.obj W :=
      Sigma.desc (fun x => Y.map (ri (idx x) ≫ kk x))
    have hafac : aa ≫ q = Sigma.desc (fun x : UR.left.obj => Y.map (pp x)) ≫ tR := by
      apply Sigma.hom_ext
      intro x
      simp only [aa, Sigma.ι_comp_desc_assoc, Y.map_comp, Category.assoc]
      rw [show Y.map (kk x) ≫ q = gi (idx x) from hkq x]
      exact hfac (idx x)
    have : Presheaf.IsLocallySurjective J (aa ≫ q) := by rw [hafac]; infer_instance
    exact Presheaf.isLocallySurjective_of_isLocallySurjective J aa q
  exact ⟨W, q, relative_surjective_of_locallySurjective B S hS q hqrep hqsurj, hqet⟩

/-! ### The union of the images of the chart reductions -/

/-- A relative property holds of an identity as soon as it holds of every isomorphism and the
functor reflects isomorphisms. -/
private theorem relative_id_of_isomorphisms {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.ReflectsIsomorphisms] (P : MorphismProperty C)
    (hP : MorphismProperty.isomorphisms C ≤ P) (Z : D) : P.relative F (𝟙 Z) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso F _, ?_⟩
  intro a b g fst snd hp
  have : IsIso (F.map snd) := hp.isIso_snd_of_isIso
  have : IsIso snd := isIso_of_reflects_iso snd F
  exact hP snd inferInstance

/-- A reduced object of the site presents a reduced algebraic space. -/
theorem hasEtaleLocalPropertyULift_isReduced_uliftYoneda (T : BigFppfOver B S hS)
    (hT : IsReduced ((BigFppfOver.toScheme B S hS).obj T)) :
    Space.HasEtaleLocalPropertyULift.{u + 1} B S hS (uliftYoneda.{u + 1}.obj T)
      (fun V : Scheme.{u} => IsReduced V) := by
  refine ⟨T, 𝟙 _, ?_, ?_, hT⟩
  · apply relative_id_of_isomorphisms
    intro A C c hc
    have : IsIso c := hc
    change Surjective ((BigFppfOver.toScheme B S hS).map c)
    infer_instance
  · apply relative_id_of_isomorphisms
    intro A C c hc
    have : IsIso c := hc
    change Etale ((BigFppfOver.toScheme B S hS).map c)
    infer_instance

/-- **The preimage of the sheafified union of the images under one member of the family is the
image of that member.** The hypothesis `hsat` is that a section of `Y j` matched by a section of
some `Z i` already lies in the image of `Z j`; `Z j` being a subsheaf of `Y j`, the sheafified
union then pulls back to exactly that image. -/
private theorem preimage_sheafify_iSup_range_eq_range
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    {Ix : Type*} {Z₀ : Sheaf J (Type (u + 1))}
    {Y Z : Ix → Sheaf J (Type (u + 1))} (c : ∀ i, Y i ⟶ Z₀) (r : ∀ i, Z i ⟶ Y i)
    [∀ i, Mono (r i)]
    (hsat : ∀ i j (T : Cᵒᵖ) (x : (Z i).obj.obj T) (y : (Y j).obj.obj T),
      ((r i ≫ c i).hom.app T) x = (c j).hom.app T y →
        y ∈ (Subfunctor.range (r j).hom).obj T)
    (j : Ix) :
    ((⨆ i, Subfunctor.range (r i ≫ c i).hom).sheafify J).preimage (c j).hom =
      Subfunctor.range (r j).hom := by
  let A : Subfunctor Z₀.obj := ⨆ i, Subfunctor.range (r i ≫ c i).hom
  have hrmono : Mono (r j).hom := (sheafToPresheaf J (Type (u + 1))).map_mono (r j)
  have hR : Presieve.IsSheaf J (Subfunctor.range (r j).hom).toFunctor :=
    (isSheaf_iff_isSheaf_of_type J _).1
      ((Presheaf.isSheaf_of_iso_iff (asIso (Subfunctor.toRange (r j).hom))).1 (Z j).property)
  ext T y
  constructor
  · intro hy
    apply ((Subfunctor.range (r j).hom).isSheaf_iff
      ((isSheaf_iff_isSheaf_of_type J _).1 (Y j).property)).1 hR T y
    change A.sieveOfSection ((c j).hom.app T y) ∈ J T.unop at hy
    apply J.superset_covering ?_ hy
    intro V h hh
    change Z₀.obj.map h.op ((c j).hom.app T y) ∈ A.obj (op V) at hh
    simp only [A, Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.range_obj] at hh
    obtain ⟨i, x, hx⟩ := hh
    exact hsat i j (op V) x _ (hx.trans ((c j).hom.naturality_apply h.op y).symm)
  · rintro ⟨x, rfl⟩
    apply A.le_sheafify J
    change ((r j ≫ c j).hom.app T) x ∈ A.obj T
    exact (le_iSup (fun i => Subfunctor.range (r i ≫ c i).hom) j) T ⟨x, rfl⟩

/-- A subobject whose preimage under a morphism is the image of a monomorphism makes the
evident square cartesian. -/
private theorem isPullback_of_preimage_eq_range
    {C : Type*} [Category C] {F U V : C ⥤ Type (u + 1)}
    (G : Subfunctor F) (r : U ⟶ V) [Mono r] (c : V ⟶ F)
    (l : U ⟶ G.toFunctor) (hl : l ≫ G.ι = r ≫ c)
    (heq : G.preimage c = Subfunctor.range r) : IsPullback l r G.ι c := by
  refine IsPullback.mk' hl (fun _ _ _ _ h => (cancel_mono r).1 h) ?_
  · intro T x y hxy
    have hb : Subfunctor.range y ≤ Subfunctor.range r := by
      rw [← heq]
      intro V' z hz
      obtain ⟨t, rfl⟩ := hz
      have h := ConcreteCategory.congr_hom (congr_app hxy V') t
      change (x.app V' t).val = (c.app V') (y.app V' t) at h
      change (c.app V') (y.app V' t) ∈ G.obj V'
      rw [← h]
      exact (x.app V' t).property
    let lift := Subfunctor.lift y hb ≫ inv (Subfunctor.toRange r)
    have hlift : lift ≫ r = y := by
      have hi : inv (Subfunctor.toRange r) ≫ r = (Subfunctor.range r).ι :=
        (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι r).symm
      simp only [lift, Category.assoc, hi, Subfunctor.lift_ι]
    refine ⟨lift, ?_, hlift⟩
    apply (cancel_mono G.ι).1
    rw [Category.assoc, hl, ← Category.assoc, hlift, hxy]

/-! ### Stacks 0AIN -/

/-- Let `X` be a formal algebraic space over `S`. There exists a reduced algebraic space `X_red`
and a representable morphism `X_red ⟶ X` which is a thickening, and a morphism `U ⟶ X` with `U`
a reduced algebraic space factors uniquely through `X_red`. -/
@[stacks 0AIN "a general formal algebraic space"]
theorem exists_isReduction_of_isFormalAlgebraicSpace
    (X : FppfSheaf B S hS) (hX : IsFormalAlgebraicSpace B S hS X) :
    ∃ (Xred : FppfSheaf B S hS) (i : Xred ⟶ X), IsReduction B S hS X Xred i := by
  classical
  let J := BigFppfOver.topology B S hS
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, I, Xi, f, hXi, hf, hcover⟩ := id hX
  choose Ti ri hTiaff hTired hriU using
    fun i => exists_siteReduction_of_isAffineFormalAlgebraicSpace B S hS (Xi i) (hXi i)
  let Rsp (i : I) : FppfSheaf B S hS :=
    ⟨uliftYoneda.{u + 1}.obj (Ti i),
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS (Ti i)).isSheaf⟩
  let jj (i : I) : Rsp i ⟶ Xi i := (sheafificationIso (Rsp i)).hom ≫ ri i
  have hjj (i : I) : Space.IsRepresentableThickeningULift.{u + 1} B S hS (jj i).hom := by
    have : (MorphismProperty.relative uliftYoneda.{u + 1}
        (MorphismProperty.inverseImage
          (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))).RespectsIso :=
      (MorphismProperty.relative_isStableUnderBaseChange (F := uliftYoneda.{u + 1})
        (MorphismProperty.inverseImage
          (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))).respectsIso
    exact MorphismProperty.RespectsIso.precomp _ (sheafificationIso (Rsp i)).hom.hom
      (ri i).hom (hriU i)
  have hjjmono (i : I) : Mono (jj i) :=
    (sheafToPresheaf J (Type (u + 1))).mono_of_mono_map
      (mono_of_isRepresentableThickeningULift B S hS (hjj i))
  have hRi (i : I) : IsReduction B S hS (Xi i) (Rsp i) (jj i) :=
    isReduction_of_isRepresentableThickening B S hS (jj i)
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS (Ti i))
      (hasEtaleLocalPropertyULift_isReduced_uliftYoneda B S hS (Ti i) (hTired i))
      (hjj i)
  let A : Subfunctor X.obj := ⨆ i, Subfunctor.range (jj i ≫ f i).hom
  let R : FppfSheaf B S hS := ⟨(A.sheafify J).toFunctor,
    (isSheaf_iff_isSheaf_of_type J _).2
      (A.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type J _).1 X.property))⟩
  let ι : R ⟶ X := ⟨(A.sheafify J).ι⟩
  have hle (i : I) : Subfunctor.range (jj i ≫ f i).hom ≤ A.sheafify J :=
    (le_iSup (fun i => Subfunctor.range (jj i ≫ f i).hom) i).trans (A.le_sheafify J)
  let k (i : I) : Rsp i ⟶ R := ⟨Subfunctor.lift (jj i ≫ f i).hom (hle i)⟩
  have hk (i : I) : k i ≫ ι = jj i ≫ f i :=
    (sheafToPresheaf J (Type (u + 1))).map_injective (Subfunctor.lift_ι (jj i ≫ f i).hom (hle i))
  have hsat : ∀ i j (T : (BigFppfOver B S hS)ᵒᵖ) (x : (Rsp i).obj.obj T)
      (y : (Xi j).obj.obj T),
      ((jj i ≫ f i).hom.app T) x = (f j).hom.app T y →
        y ∈ (Subfunctor.range (jj j).hom).obj T := by
    intro i j T x y hxy
    obtain ⟨hrep, het⟩ := hf j
    obtain ⟨q, hq, -⟩ := exists_lift_reduced_chart_overlap B S hS (f j) hrep het
      (hRi j) (Ti i) (hTired i) ((jj i ≫ f i).hom)
    have hs := (IsPullback.of_hasPullback ((jj i ≫ f i).hom) (f j).hom).map
      ((evaluation (BigFppfOver B S hS)ᵒᵖ (Type (u + 1))).obj T)
    obtain ⟨c, -, hc⟩ := Types.exists_of_isPullback hs x y hxy
    exact ⟨q.app T c, (ConcreteCategory.congr_hom (congr_app hq T) c).trans hc⟩
  have hsq (i : I) : IsPullback (k i) (jj i) ι (f i) := by
    have heq := preimage_sheafify_iSup_range_eq_range J f jj hsat i
    have hpre := isPullback_of_preimage_eq_range (A.sheafify J) (jj i).hom (f i).hom
      (k i).hom (congrArg (fun t : Rsp i ⟶ X => t.hom) (hk i)) heq
    exact hpre.of_map (sheafToPresheaf J (Type (u + 1))) (hk i)
  have hcoverR : Sheaf.IsLocallySurjective (Sigma.desc k) := by
    refine ⟨fun {T} x => ?_⟩
    change Presheaf.imageSieve (Sigma.desc k).hom x ∈ J T
    apply J.superset_covering ?_ x.property
    intro V h hh
    change X.obj.map h.op x.val ∈ A.obj (op V) at hh
    simp only [A, Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.range_obj] at hh
    obtain ⟨i, y, hy⟩ := hh
    refine ⟨(Sigma.ι (fun i => Rsp i) i).hom.app (op V) y, ?_⟩
    apply Subtype.ext
    have he : Sigma.ι (fun i => Rsp i) i ≫ Sigma.desc k ≫ ι = jj i ≫ f i := by
      rw [Sigma.ι_comp_desc_assoc, hk]
    exact (ConcreteCategory.congr_hom
      (congr_app (congrArg (fun t : Rsp i ⟶ X => t.hom) he) (op V)) y).trans hy
  have hιmonoP : Mono ι.hom := by
    change Mono (A.sheafify J).ι
    infer_instance
  have hιthick : Space.IsRepresentableThickeningULift.{u + 1} B S hS ι.hom :=
    isRepresentableThickeningULift_of_isPullback_etale_cover B S hS ι hιmonoP
      Xi Rsp f k jj hsq hf hcover hjj
  have halg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS R.obj :=
    isAlgebraicSpaceULift_of_reduced_etale_cover B S hS ι hιmonoP hX Xi Rsp Ti hTiaff
      (fun i => Iso.refl _) f k jj hsq hf hcoverR hιthick
  have hred : Space.HasEtaleLocalPropertyULift.{u + 1} B S hS R.obj
      (fun T : Scheme.{u} => IsReduced T) := by
    obtain ⟨T, atlas, hs, he⟩ := halg.exists_atlas
    exact ⟨T, atlas, hs, he,
      isReduced_of_isEtale_into_sheafified_iSup_range B S hS X.obj Ti hTired
        (fun i => (jj i ≫ f i).hom) T atlas he⟩
  exact ⟨R, ι, isReduction_of_isRepresentableThickening B S hS ι halg hred hιthick⟩

end AlgebraicGeometry.FormalSpace

end
