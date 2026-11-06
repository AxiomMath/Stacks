module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSiteChart
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAmalgamation

/-!
# Étale charts of a formal algebraic space through a point, and cartesian squares of sheaves

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a formal algebraic space over
`S` with atlas `{X_i ⟶ X}`, and let `g : h_a ⟶ X` be a scheme-valued point. Through every point
of `a` there is an affine étale chart of `a` over which `g` factors through some `X_i`; over such
a chart the base change of a subobject `ι : R ⟶ X` whose base changes to the `X_i` are
representable thickenings is represented by a thickening. A commuting square of fppf sheaves with
monomorphic right leg each of whose sections lifts locally is cartesian.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_factorization_through_point_uliftYoneda`: every point of
  a site object carrying a scheme-valued point of `X` lies in the image of a site object over
  which that point factors through one member of the atlas.
* `AlgebraicGeometry.FormalSpace.exists_etale_affine_chart_through_point`: an affine étale
  chart of `a` through a prescribed point, still factoring through a member of the atlas.
* `AlgebraicGeometry.FormalSpace.exists_thickening_chart_of_isPullback`: over such a chart the
  base change of `ι` is represented by a thickening.
* `AlgebraicGeometry.FormalSpace.isPullback_of_mono_of_local_lift_presheaf`: a commuting square
  of fppf sheaves with monomorphic right leg each of whose sections lifts locally is cartesian.
* `AlgebraicGeometry.FormalSpace.mono_uliftYoneda_map`: the universe-lifted Yoneda embedding
  preserves monomorphisms.

## References

* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Charts of a formal algebraic space through a prescribed point -/

/-- Every point of a site object `a` carrying a scheme-valued point `g` of a formal algebraic
space lies in the image of a site object over which `g` factors through one member of the atlas,
the points being taken relative to the universe-lifted Yoneda embedding of presheaves. -/
theorem exists_factorization_through_point_uliftYoneda
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)]
    {X : FppfSheaf B S hS} {I : Type (u + 1)} (Xi : I → FppfSheaf B S hS)
    (f : ∀ i, Xi i ⟶ X) (hcover : Sheaf.IsLocallySurjective (Limits.Sigma.desc f))
    (a : BigFppfOver B S hS) (g : (uliftYoneda.{u + 1}).obj a ⟶ X.obj)
    (x : (BigFppfOver.toScheme B S hS).obj a) :
    ∃ (i : I) (T : BigFppfOver B S hS) (b : T ⟶ a)
      (m : (uliftYoneda.{u + 1}).obj T ⟶ (Xi i).obj)
      (y : (BigFppfOver.toScheme B S hS).obj T),
      m ≫ (f i).hom = (uliftYoneda.{u + 1}).map b ≫ g ∧
        (BigFppfOver.toScheme B S hS).map b y = x := by
  classical
  have hmem := Sheaf.iSup_imageSieve_mem_of_isLocallySurjective_sigmaDesc
    (BigFppfOver.topology B S hS) Xi X f hcover a (uliftYonedaEquiv g)
  obtain ⟨T, b, y, hb, hy⟩ := exists_mem_sieve_point B S hS hmem x
  simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hb
  obtain ⟨-, ⟨i, rfl⟩, z, hz⟩ := hb
  refine ⟨i, T, b, uliftYonedaEquiv.symm z, y, uliftYonedaEquiv.injective ?_, hy⟩
  rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  exact hz.trans (uliftYonedaEquiv_naturality.{u + 1} g b.op)

/-- A scheme-valued point `g : h_a ⟶ X` which factors through a member `X_i` of the atlas over a
site object `T` admits, through any prescribed point of `T`, an affine chart of `a` which is
étale over `a`, hits the image of that point, and still factors through `X_i`. -/
theorem exists_etale_affine_chart_through_point
    {X Xi : FppfSheaf B S hS} (fi : Xi ⟶ X)
    (hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS fi.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom) fi.hom hfi)
    (a : BigFppfOver B S hS) (g : (uliftYoneda.{u + 1}).obj a ⟶ X.obj)
    (T : BigFppfOver B S hS) (b : T ⟶ a)
    (m : (uliftYoneda.{u + 1}).obj T ⟶ Xi.obj)
    (hm : m ≫ fi.hom = (uliftYoneda.{u + 1}).map b ≫ g)
    (y : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ (A : BigFppfOver B S hS) (c : A ⟶ a) (φ : (uliftYoneda.{u + 1}).obj A ⟶ Xi.obj),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
        Etale ((BigFppfOver.toScheme B S hS).map c) ∧
          (BigFppfOver.toScheme B S hS).map b y ∈
              Set.range ((BigFppfOver.toScheme B S hS).map c) ∧
            φ ≫ fi.hom = (uliftYoneda.{u + 1}).map c ≫ g := by
  classical
  obtain ⟨Ua, t, hts, hte⟩ := (hfi a g).exists_atlas
  let ca : Ua ⟶ a := (uliftYoneda.{u + 1}).preimage (t ≫ pullback.fst g fi.hom)
  have hcaeq : (uliftYoneda.{u + 1}).map ca = t ≫ pullback.fst g fi.hom :=
    (uliftYoneda.{u + 1}).map_preimage _
  have hcaP : (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) ca :=
    MorphismProperty.of_relative_map (F := uliftYoneda.{u + 1})
      (by rw [hcaeq]; exact het a g Ua t hte)
  have : Etale ((BigFppfOver.toScheme B S hS).map ca) := hcaP
  have hφa : (t ≫ pullback.snd g fi.hom) ≫ fi.hom =
      (uliftYoneda.{u + 1}).map ca ≫ g := by
    rw [hcaeq, Category.assoc, Category.assoc, pullback.condition]
  let θ : (uliftYoneda.{u + 1}).obj T ⟶ pullback g fi.hom :=
    pullback.lift ((uliftYoneda.{u + 1}).map b) m hm.symm
  have hθf : θ ≫ pullback.fst g fi.hom = (uliftYoneda.{u + 1}).map b :=
    pullback.lift_fst _ _ _
  have hprs : Surjective ((BigFppfOver.toScheme B S hS).map (hts.rep.snd θ)) :=
    hts.property_snd θ
  let ra : hts.rep.pullback θ ⟶ Ua := (uliftYoneda.{u + 1}).preimage (hts.rep.fst θ)
  have hra : ra ≫ ca = hts.rep.snd θ ≫ b := by
    apply (uliftYoneda.{u + 1}).map_injective
    rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, hcaeq,
      ← Category.assoc, (hts.rep.isPullback θ).w, Category.assoc, hθf]
  obtain ⟨y', hy'⟩ := hprs.surj y
  obtain ⟨A, iA, hAaff, hiA, hmemA, -⟩ := exists_affineOpen_site_object B S hS Ua
    ((BigFppfOver.toScheme B S hS).map ra y')
  refine ⟨A, iA ≫ ca, (uliftYoneda.{u + 1}).map iA ≫ (t ≫ pullback.snd g fi.hom),
    hAaff, ?_, ?_, ?_⟩
  · rw [Functor.map_comp]
    have _ : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map iA) := hiA
    infer_instance
  · obtain ⟨z, hz⟩ := hmemA
    refine ⟨z, ?_⟩
    have h3 : (BigFppfOver.toScheme B S hS).map (ra ≫ ca) y' =
        (BigFppfOver.toScheme B S hS).map (hts.rep.snd θ ≫ b) y' := by rw [hra]
    rw [Functor.map_comp] at h3 ⊢
    show (BigFppfOver.toScheme B S hS).map ca ((BigFppfOver.toScheme B S hS).map iA z) = _
    rw [hz]
    refine h3.trans ?_
    show (BigFppfOver.toScheme B S hS).map b
      ((BigFppfOver.toScheme B S hS).map (hts.rep.snd θ) y') = _
    rw [hy']
  · rw [Category.assoc, hφa, ← Category.assoc, ← Functor.map_comp]

/-- Let `R_i = R ×_X X_i` with `R_i ⟶ X_i` a representable thickening. Over a chart of `a` whose
composite into `X` factors through `X_i`, the base change of `ι` is represented by a
thickening. -/
theorem exists_thickening_chart_of_isPullback
    {X R Xi Ri : FppfSheaf B S hS} (ι : R ⟶ X) (fi : Xi ⟶ X) (ki : Ri ⟶ R) (ji : Ri ⟶ Xi)
    (hsq : IsPullback ki ji ι fi)
    (hj : Space.IsRepresentableThickeningULift.{u + 1} B S hS ji.hom)
    {a : BigFppfOver B S hS} (g : (uliftYoneda.{u + 1}).obj a ⟶ X.obj)
    (A : BigFppfOver B S hS) (c : A ⟶ a)
    (φ : (uliftYoneda.{u + 1}).obj A ⟶ Xi.obj)
    (hφ : φ ≫ fi.hom = (uliftYoneda.{u + 1}).map c ≫ g) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ A)
      (v : (uliftYoneda.{u + 1}).obj V ⟶ R.obj),
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map p) ∧
        IsPullback v ((uliftYoneda.{u + 1}).map p) ι.hom
          ((uliftYoneda.{u + 1}).map c ≫ g) := by
  have hsqP : IsPullback ki.hom ji.hom ι.hom fi.hom :=
    hsq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  have hbig := (hj.rep.isPullback φ).paste_horiz hsqP
  rw [hφ] at hbig
  exact ⟨hj.rep.pullback φ, hj.rep.snd φ, hj.rep.fst φ ≫ ki.hom, hj.property_snd φ, hbig⟩

/-! ### Being a cartesian square is local on the base -/

/-- A commuting square of fppf sheaves whose right-hand leg is a monomorphism and each of whose
sections lifts locally is cartesian. -/
private theorem isPullback_of_mono_of_local_lift_sheaf
    {P F G H : FppfSheaf B S hS} (fst : P ⟶ F) (snd : P ⟶ G) (f : F ⟶ H) (g : G ⟶ H)
    (hcomm : fst ≫ f = snd ≫ g) (hmono : Mono snd.hom)
    (hlift : ∀ (T : BigFppfOver B S hS) (x : F.obj.obj (Opposite.op T))
      (y : G.obj.obj (Opposite.op T)),
      f.hom.app (Opposite.op T) x = g.hom.app (Opposite.op T) y →
      ∃ W ∈ BigFppfOver.topology B S hS T,
        ∀ ⦃T' : BigFppfOver B S hS⦄ (h : T' ⟶ T), W h →
          ∃ z : P.obj.obj (Opposite.op T'),
            fst.hom.app (Opposite.op T') z = F.obj.map h.op x ∧
              snd.hom.app (Opposite.op T') z = G.obj.map h.op y) :
    IsPullback fst snd f g := by
  let J := BigFppfOver.topology B S hS
  let θ : P ⟶ pullback f g := pullback.lift fst snd hcomm
  have hθsnd : θ ≫ pullback.snd f g = snd := pullback.lift_snd _ _ _
  have hθfst : θ ≫ pullback.fst f g = fst := pullback.lift_fst _ _ _
  have hθapp : ∀ {Q : FppfSheaf B S hS} (p : pullback f g ⟶ Q) (q : P ⟶ Q), θ ≫ p = q →
      ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (z : P.obj.obj T),
        p.hom.app T (θ.hom.app T z) = q.hom.app T z := fun p q h T z ↦ by
    simpa using ConcreteCategory.congr_hom (congr_app (congrArg (·.hom) h) T) z
  have hinj : ∀ T : (BigFppfOver B S hS)ᵒᵖ, Function.Injective (θ.hom.app T) := by
    intro T z z' hz
    refine ((mono_iff_injective (snd.hom.app T)).1
      ((NatTrans.mono_iff_mono_app snd.hom).1 hmono T)) ?_
    rw [← hθapp _ _ hθsnd T z, ← hθapp _ _ hθsnd T z', hz]
  have hlocinj : Presheaf.IsLocallyInjective J θ.hom := by
    refine ⟨fun {T} z z' hz ↦ ?_⟩
    obtain rfl := hinj T hz
    exact J.superset_covering (fun _ _ _ ↦ rfl) (J.top_mem T.unop)
  have hpbP : IsPullback (pullback.fst f g).hom (pullback.snd f g).hom f.hom g.hom :=
    (IsPullback.of_hasPullback f g).map (sheafToPresheaf J (Type (u + 1)))
  have hlocsurj : Presheaf.IsLocallySurjective J θ.hom := by
    refine ⟨fun {T} s ↦ ?_⟩
    have hxy : f.hom.app (Opposite.op T) ((pullback.fst f g).hom.app (Opposite.op T) s) =
        g.hom.app (Opposite.op T) ((pullback.snd f g).hom.app (Opposite.op T) s) := by
      simpa using ConcreteCategory.congr_hom (congr_app hpbP.w (Opposite.op T)) s
    obtain ⟨W, hW, hlifts⟩ := hlift T
      ((pullback.fst f g).hom.app (Opposite.op T) s)
      ((pullback.snd f g).hom.app (Opposite.op T) s) hxy
    refine J.superset_covering ?_ hW
    intro T' h hh
    obtain ⟨z, hz1, hz2⟩ := hlifts h hh
    refine ⟨z, Types.ext_of_isPullback (hpbP.app (Opposite.op T')) ?_ ?_⟩
    · rw [NatTrans.naturality_apply (pullback.fst f g).hom h.op s, ← hz1]
      exact hθapp _ _ hθfst _ z
    · rw [NatTrans.naturality_apply (pullback.snd f g).hom h.op s, ← hz2]
      exact hθapp _ _ hθsnd _ z
  have : IsIso θ := (Sheaf.isLocallyBijective_iff_isIso θ).1 ⟨hlocinj, hlocsurj⟩
  exact IsPullback.of_iso_pullback ⟨hcomm⟩ (asIso θ) hθfst hθsnd

/-- A commuting square of presheaves on the big fppf site of `S`, all four of whose corners are
sheaves, whose right-hand leg is a monomorphism and each of whose sections lifts locally, is
cartesian. -/
theorem isPullback_of_mono_of_local_lift_presheaf
    {Pp Fp Gp Hp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hPp : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Pp)
    (hFp : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Fp)
    (hGp : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Gp)
    (hHp : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Hp)
    (fst : Pp ⟶ Fp) (snd : Pp ⟶ Gp) (f : Fp ⟶ Hp) (g : Gp ⟶ Hp)
    (hcomm : fst ≫ f = snd ≫ g) (hmono : Mono snd)
    (hlift : ∀ (T : BigFppfOver B S hS) (x : Fp.obj (Opposite.op T))
      (y : Gp.obj (Opposite.op T)),
      f.app (Opposite.op T) x = g.app (Opposite.op T) y →
      ∃ W ∈ BigFppfOver.topology B S hS T,
        ∀ ⦃T' : BigFppfOver B S hS⦄ (h : T' ⟶ T), W h →
          ∃ z : Pp.obj (Opposite.op T'),
            fst.app (Opposite.op T') z = Fp.map h.op x ∧
              snd.app (Opposite.op T') z = Gp.map h.op y) :
    IsPullback fst snd f g :=
  (isPullback_of_mono_of_local_lift_sheaf B S hS
    (P := ⟨Pp, hPp⟩) (F := ⟨Fp, hFp⟩) (G := ⟨Gp, hGp⟩) (H := ⟨Hp, hHp⟩)
    ⟨fst⟩ ⟨snd⟩ ⟨f⟩ ⟨g⟩ (Sheaf.hom_ext hcomm) hmono hlift).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))

/-- The universe-lifted Yoneda presheaf of a monomorphism of site objects is a monomorphism of
presheaves. -/
theorem mono_uliftYoneda_map {V W : BigFppfOver B S hS} (p : V ⟶ W) (hp : Mono p) :
    Mono ((uliftYoneda.{u + 1}).map p) :=
  (NatTrans.mono_iff_mono_app _).2 fun _ ↦ (mono_iff_injective _).2 fun _ _ hs ↦
    ULift.ext ((cancel_mono p).mp (congrArg ULift.down hs))

end AlgebraicGeometry.FormalSpace

end
