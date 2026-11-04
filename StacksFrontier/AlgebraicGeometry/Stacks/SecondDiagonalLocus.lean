module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.SurjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonalAutomorphism
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheafVertHom

/-!
# The locus where an automorphism is trivial is a scheme

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S` whose second
diagonal `Δ_Δ : 𝒳 ⟶ 𝒳 ×_{𝒳 × 𝒳} 𝒳` is representable by algebraic spaces, and which is limit
preserving. Let `x` be an object of `𝒳` over `U` and `θ` a vertical automorphism of `x`. Then the
locus where `θ` is trivial is represented by a monomorphism of schemes `Z ⟶ U` which is locally
of finite type: an arrow `c : a ⟶ x` of `𝒳` lies over a morphism factoring through `Z` exactly
when `c ≫ θ = c`.

This is the reading of condition (1) of Stacks 07WG used in the proof of Stacks 0G2K: the
condition `θ = 𝟙` defines an algebraic space `W` over `U` with `W ⟶ U` a monomorphism
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_secondDiagonal_iff_automorphism`).
Limit preservation makes `W ⟶ U` locally of finite presentation by the criterion of
Stacks 0CM6, as in Stacks 0CXI: an equality of vertical morphisms over an affine limit already
holds at a stage. A monomorphism locally of finite type is locally quasi-finite and separated
(Stacks 0463 and 042N), hence representable by Stacks 03XX.

## Main results

* `AlgebraicGeometry.Stack.exists_mono_locallyOfFiniteType_trivialLocus`: the locus where a
  vertical automorphism is trivial is a monomorphism of schemes locally of finite type.

## References

* [Stacks Project, Tag 07WG](https://stacks.math.columbia.edu/tag/07WG)
* [Stacks Project, Tag 0CXI](https://stacks.math.columbia.edu/tag/0CXI)
* [Stacks Project, Tag 0CM6](https://stacks.math.columbia.edu/tag/0CM6)
* [Stacks Project, Tag 0463](https://stacks.math.columbia.edu/tag/0463)
* [Stacks Project, Tag 03XX](https://stacks.math.columbia.edu/tag/03XX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

universe u

attribute [local implicit_reducible] CategoryTheory.TwoFibreProductOver.fst
  CategoryTheory.TwoFibreProductOver.snd CategoryTheory.TwoFibreProductOver.diagonal

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- A filtered colimit of subsingletons is a subsingleton. -/
theorem subsingleton_colimit_of_subsingleton {J : Type u} [Category.{u} J] [IsFiltered J]
    (G : J ⥤ Type u) [HasColimit G] (hG : ∀ j, Subsingleton (G.obj j)) :
    Subsingleton (colimit G) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨i, x, rfl⟩ := Types.jointly_surjective' a
  obtain ⟨j, y, rfl⟩ := Types.jointly_surjective' b
  rw [← colimit.w_apply (F := G) (IsFiltered.leftToMax i j) x,
    ← colimit.w_apply (F := G) (IsFiltered.rightToMax i j) y,
    (hG (IsFiltered.max i j)).elim (G.map (IsFiltered.leftToMax i j) x)
      (G.map (IsFiltered.rightToMax i j) y)]

/-- A vertical endomorphism `θ` of `x` restricts along every arrow `φ : z ⟶ x`, and the
restriction is trivial exactly when `φ ≫ θ = φ`. -/
theorem eq_id_iff_of_comp_eq {C : Type*} [Category C] {X : Type*} [Category X] (p : X ⥤ C)
    (hp : p.IsFiberedInGroupoids) {R T : C} (f : R ⟶ T) {z x : X} (φ : z ⟶ x)
    (hφ : p.IsHomLift f φ) (θ : x ⟶ x) (hθ : p.IsHomLift (𝟙 T) θ) (θ' : z ⟶ z)
    (hθ' : p.IsHomLift (𝟙 R) θ') (h : φ ≫ θ = θ' ≫ φ) : θ' = 𝟙 z ↔ φ ≫ θ = φ := by
  have : p.IsStronglyCartesian f φ := hp.isStronglyCartesian_homLift f φ
  constructor
  · rintro rfl
    rw [h, Category.id_comp]
  · intro h'
    have : p.IsHomLift (𝟙 R) (𝟙 z) := IsHomLift.id (IsHomLift.domain_eq p f φ)
    exact Functor.IsStronglyCartesian.ext p f φ (𝟙 R) (by rw [← h, h', Category.id_comp])

/-- Precomposition with an isomorphism does not change whether `θ` fixes a morphism. -/
theorem comp_eq_self_iff_of_isIso {C : Type*} [Category C] {w z x : C} (v : w ⟶ z) [IsIso v]
    (φ : z ⟶ x) (θ : x ⟶ x) : (v ≫ φ) ≫ θ = v ≫ φ ↔ φ ≫ θ = φ := by
  rw [Category.assoc]
  exact ⟨fun h => (cancel_epi v).mp h, fun h => by rw [h]⟩

/-- A morphism of a category fibred in groupoids lying over an isomorphism is invertible. -/
private theorem isIso_of_isHomLift_of_isIso {C : Type*} [Category C] {X : Type*} [Category X]
    (p : X ⥤ C) (hp : p.IsFiberedInGroupoids) {R T : C} (f : R ⟶ T) [IsIso f] {z x : X}
    (φ : z ⟶ x) [p.IsHomLift f φ] : IsIso φ := by
  have := hp.isStronglyCartesian_homLift f φ
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p f φ

/-- **The locus where a vertical automorphism is trivial.** Let `𝒳` be limit preserving with
second diagonal representable by algebraic spaces. For an object `x` of `𝒳` and a vertical
automorphism `θ` of `x`, there are a scheme `Z` of the site and a monomorphism `ι : Z ⟶ U`
locally of finite type, `U` the scheme under `x`, such that an arrow `c : a ⟶ x` lies over a
morphism factoring through `ι` exactly when `c ≫ θ = c`. -/
theorem exists_mono_locallyOfFiniteType_trivialLocus
    (h1 : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalBasedFunctor B S hS 𝒳 (CatFiberedInGroupoids.product 𝒳 𝒳)
        (diagonalBasedFunctor B S hS 𝒳)))
    (h3 : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    (x : 𝒳.val.obj) (θ : x ⟶ x) (hθ : 𝒳.val.p.map θ = 𝟙 _) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ (BigFppfOver.toScheme B S hS).obj (𝒳.val.p.obj x)),
      Mono ι ∧ LocallyOfFiniteType ι ∧ B.Contains Z ∧
      ∀ (a : 𝒳.val.obj) (c : a ⟶ x),
        (∃ g : (BigFppfOver.toScheme B S hS).obj (𝒳.val.p.obj a) ⟶ Z,
          g ≫ ι = (BigFppfOver.toScheme B S hS).map (𝒳.val.p.map c)) ↔ c ≫ θ = c := by
  classical
  have hp : 𝒳.val.p.IsFiberedInGroupoids := 𝒳.isFiberedInGroupoids
  let : 𝒳.val.p.IsFibered := hp.isFibered
  let P := 𝒳.val.p.obj x
  let Vs := BigFppfOver.toScheme B S hS
  have hG : 𝒳.val.p ⋙ 𝟭 _ = 𝒳.val.p := Functor.comp_id _
  have : 𝒳.val.p.IsHomLift (𝟙 P) θ := IsHomLift.of_fac' 𝒳.val.p _ θ rfl rfl (by simpa using hθ)
  have : IsIso θ := isIso_of_isHomLift_of_isIso 𝒳.val.p hp (𝟙 P) θ
  let A : RelativeInertia 𝒳.val.p := ⟨x, asIso θ, hθ⟩
  let pt : DiagonalFibreProduct hG := (ofRelativeInertia hG).obj A
  let pZ := RelativeDiagonalFibre.RelProdP 𝒳.val.p (CatFiberedInGroupoids.product 𝒳 𝒳).val.p
    (diagonalBasedFunctor B S hS 𝒳).toFunctor
  have hpZ : pZ.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids 𝒳.val.p 𝒳.val.p
      (CatFiberedInGroupoids.product 𝒳 𝒳).val.p
      (diagonalBasedFunctor B S hS 𝒳).toFunctor (diagonalBasedFunctor B S hS 𝒳).toFunctor hp hp
      (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids
      (diagonalBasedFunctor B S hS 𝒳).w (diagonalBasedFunctor B S hS 𝒳).w
  let : pZ.IsFibered := hpZ.isFibered
  let pt' : pZ.Fiber P := ⟨pt, rfl⟩
  let Y := Over.iteratedSliceBackward P ⋙ Functor.pullbackSliceFunctor pZ pt'
  have hY : Y ⋙ pZ = Over.map P.hom := Functor.backward_pullbackSliceFunctor_comp pZ P pt'
  -- `Y` sends a morphism of the site to an arrow of `𝒳` lying over its image
  have hYa : ∀ {T T' : BigFppfOver B P.left.1 P.left.2} (f : T ⟶ T'),
      𝒳.val.p.IsHomLift ((Over.map P.hom).map f) (Y.map f).a := by
    intro T T' f
    have h₁ := (Y.map f).ha
    have h₂ : (Y.map f).hbase = eqToHom (Functor.congr_obj hY T) ≫
        (Over.map P.hom).map f ≫ eqToHom (Functor.congr_obj hY T').symm :=
      Functor.congr_hom hY f
    rw [h₂] at h₁
    exact (IsHomLift.lift_comp_eqToHom_iff (p := 𝒳.val.p) _ _ _).mp
      ((IsHomLift.lift_eqToHom_comp_iff (p := 𝒳.val.p) _ _ _).mp h₁)
  obtain ⟨F, hF, hFsub, hFsupp⟩ :=
    (isRepresentableByAlgebraicSpaces_secondDiagonal_iff_automorphism B S hS 𝒳).mp h1 P Y hY
  -- the automorphism attached to the point `pt` is `θ`
  have hdpt : (diagonalAut hG pt).hom = θ := by
    simp [pt, ofRelativeInertia, A]
  -- the canonical arrow from `Y T` to `pt`
  let g : ∀ T : BigFppfOver B P.left.1 P.left.2, (Over.map P.hom).obj T ⟶ P := fun T =>
    ((Over.iteratedSliceBackward P).obj T).hom
  let π : ∀ T : BigFppfOver B P.left.1 P.left.2, Y.obj T ⟶ pt := fun T =>
    Functor.IsPreFibered.pullbackMap pt'.2 (g T)
  have hπ (T) : pZ.IsHomLift (g T) (π T) := by
    show pZ.IsHomLift (g T) (Functor.IsPreFibered.pullbackMap pt'.2 (g T))
    infer_instance
  have hπa (T : BigFppfOver B P.left.1 P.left.2) : 𝒳.val.p.IsHomLift (g T) (π T).a := by
    have h₁ := (π T).ha
    have := hπ T
    have h₂ : (π T).hbase = eqToHom (Functor.congr_obj hY T) ≫ g T ≫ eqToHom rfl := by
      exact IsHomLift.fac' pZ (g T) (π T)
    rw [h₂] at h₁
    exact (IsHomLift.lift_comp_eqToHom_iff (p := 𝒳.val.p) _ _ _).mp
      ((IsHomLift.lift_eqToHom_comp_iff (p := 𝒳.val.p) _ _ _).mp h₁)
  have hvert : ∀ T : BigFppfOver B P.left.1 P.left.2,
      𝒳.val.p.IsHomLift (𝟙 ((Over.map P.hom).obj T)) (diagonalAut hG (Y.obj T)).hom := by
    intro T
    refine IsHomLift.of_fac' 𝒳.val.p _ _ ?_ ?_ ?_
    · exact (Y.obj T).hx.trans (Functor.congr_obj hY T)
    · exact (Y.obj T).hx.trans (Functor.congr_obj hY T)
    · exact (map_diagonalAut_hom hG (Y.obj T)).trans (by simp)
  -- the support of `F` is the locus where the restriction of `θ` is trivial
  have hsupp (T : BigFppfOver B P.left.1 P.left.2) :
      Nonempty (F.obj (op T)) ↔ (π T).a ≫ θ = (π T).a := by
    rw [hFsupp T]
    have hc := comp_diagonalAut_hom hG (π T)
    rw [hdpt] at hc
    exact eq_id_iff_of_comp_eq 𝒳.val.p hp (g T) (π T).a (hπa T) θ ‹_› _ (hvert T) hc
  -- local finite presentation of the support over the base
  have hlfp : Space.IsLocallyOfFinitePresentation B P.left.1 P.left.2
      (Space.toYonedaId B P.left.1 P.left.2 F) := by
    refine Space.isLocallyOfFinitePresentation_of_affineLimit_surjective B P.left.1 P.left.2 hF
      (isAlgebraicSpace_yoneda B P.left.1 P.left.2 _) _ ?_
    intro I _ _ D c hc hDaff hcaff xx yy _
    have : Nonempty I := IsCofiltered.nonempty
    obtain ⟨i₀⟩ := this
    -- the system over `S`
    have haff : ∀ i, IsAffineOver B S hS ((D ⋙ Over.map P.hom).obj i) := fun i => hDaff i
    have hcaff' : IsAffineOver B S hS ((Over.map P.hom).obj c.pt) := hcaff
    let D' : I ⥤ BigAffineFppf B S hS := (IsAffineOver B S hS).lift (D ⋙ Over.map P.hom) haff
    let c' : Cone D' :=
      { pt := ⟨(Over.map P.hom).obj c.pt, hcaff'⟩
        π :=
          { app := fun i => ObjectProperty.homMk ((Over.map P.hom).map (c.π.app i))
            naturality := fun i j f => by
              apply ObjectProperty.hom_ext
              show 𝟙 _ ≫ (Over.map P.hom).map (c.π.app j) =
                (Over.map P.hom).map (c.π.app i) ≫ (Over.map P.hom).map (D.map f)
              rw [Category.id_comp, ← Functor.map_comp, c.w f] } }
    have hc' : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c') := hc
    have : (Deformation.Artin.colimitComparison 𝒳.val.p (D' ⋙ BigAffineFppf.inclusion B S hS)
        ((BigAffineFppf.inclusion B S hS).mapCone c')).Faithful := (h3 I D' c' hc').faithful
    have hdesc : Deformation.Artin.DescentEq 𝒳.val.p (D ⋙ Over.map P.hom)
        ((Over.map P.hom).mapCone c) :=
      Deformation.Artin.descentEq_of_faithful 𝒳.val.p hp (D' ⋙ BigAffineFppf.inclusion B S hS)
        ((BigAffineFppf.inclusion B S hS).mapCone c')
    -- the restriction of `θ` is trivial at the cone point
    have hθpt : (diagonalAut hG (Y.obj c.pt)).hom = 𝟙 _ :=
      (hFsupp c.pt).mp ⟨xx⟩
    -- descend the equality to a stage
    let xi : 𝒳.val.p.Fiber ((D ⋙ Over.map P.hom).obj i₀) :=
      ⟨(Y.obj (D.obj i₀)).x, (Y.obj (D.obj i₀)).hx.trans (Functor.congr_obj hY _)⟩
    let xc : 𝒳.val.p.Fiber ((Over.map P.hom).mapCone c).pt :=
      ⟨(Y.obj c.pt).x, (Y.obj c.pt).hx.trans (Functor.congr_obj hY _)⟩
    have hδ : 𝒳.val.p.IsHomLift (((Over.map P.hom).mapCone c).π.app i₀) (Y.map (c.π.app i₀)).a :=
      hYa (c.π.app i₀)
    have hid : ∀ T : BigFppfOver B P.left.1 P.left.2,
        𝒳.val.p.IsHomLift (𝟙 ((Over.map P.hom).obj T)) (𝟙 (Y.obj T).x) := fun T =>
      IsHomLift.id ((Y.obj T).hx.trans (Functor.congr_obj hY T))
    obtain ⟨k, s, xk, dx, hdx, hdxe⟩ := hdesc i₀ xi xi xc (Y.map (c.π.app i₀)).a hδ
      (diagonalAut hG (Y.obj (D.obj i₀))).hom (𝟙 _) (hvert _) (hid _) (by
        have hc := comp_diagonalAut_hom hG (Y.map (c.π.app i₀))
        refine hc.trans ?_
        show (diagonalAut hG (Y.obj c.pt)).hom ≫ _ = _
        rw [hθpt, Category.id_comp, Category.comp_id])
    have hθk : (diagonalAut hG (Y.obj (D.obj k))).hom = 𝟙 _ := by
      have hmap : 𝒳.val.p.IsHomLift ((D ⋙ Over.map P.hom).map s) (Y.map (D.map s)).a :=
        hYa (D.map s)
      have := hmap
      have := hdx
      have := hvert (D.obj i₀)
      have := hvert (D.obj k)
      have : 𝒳.val.p.IsStronglyCartesian ((D ⋙ Over.map P.hom).map s) (Y.map (D.map s)).a :=
        hp.isStronglyCartesian_homLift _ _
      -- `dx` factors through the restriction map by a vertical isomorphism
      let v := Functor.IsStronglyCartesian.map 𝒳.val.p ((D ⋙ Over.map P.hom).map s)
        (Y.map (D.map s)).a (Category.id_comp _).symm dx
      have hv : v ≫ (Y.map (D.map s)).a = dx := Functor.IsStronglyCartesian.fac 𝒳.val.p _ _ _ dx
      have : IsIso v := isIso_of_isHomLift_of_isIso 𝒳.val.p hp
        (𝟙 ((D ⋙ Over.map P.hom).obj k)) v
      have hres : (Y.map (D.map s)).a ≫ (diagonalAut hG (Y.obj (D.obj i₀))).hom =
          (Y.map (D.map s)).a := by
        apply (cancel_epi v).mp
        rw [← Category.assoc, hv, hdxe, Category.comp_id]
      exact (eq_id_iff_of_comp_eq 𝒳.val.p hp ((D ⋙ Over.map P.hom).map s) (Y.map (D.map s)).a hmap
        (diagonalAut hG (Y.obj (D.obj i₀))).hom (hvert _) _ (hvert _)
        (comp_diagonalAut_hom hG (Y.map (D.map s)))).mpr hres
    obtain ⟨w⟩ := (hFsupp (D.obj k)).mpr hθk
    refine ⟨colimit.ι (D.op ⋙ F) (op k) w, ?_, ?_⟩
    · rw [colimit.ι_desc_apply]
      exact (hFsub _).elim _ _
    · have : Subsingleton (colimit (D.op ⋙ yoneda.obj (Over.mk (𝟙 (B.obj P.left.2))))) := by
        refine subsingleton_colimit_of_subsingleton _ (fun j => ?_)
        exact ⟨fun a b => Over.mkIdTerminal.hom_ext a b⟩
      exact this.elim _ _
  -- the support is a monomorphism locally of finite type, hence a scheme
  have hmono : Mono (Space.toYonedaId B P.left.1 P.left.2 F) := by
    have : ∀ T, Mono ((Space.toYonedaId B P.left.1 P.left.2 F).app T) := fun T =>
      (mono_iff_injective _).mpr (fun a b _ => (hFsub T).elim a b)
    exact NatTrans.mono_of_mono_app _
  have hlft : Space.IsLocallyOfFiniteType B P.left.1 P.left.2
      (Space.toYonedaId B P.left.1 P.left.2 F) :=
    Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B P.left.1 P.left.2 hlfp
  have hlqf := Space.isLocallyQuasiFinite_of_mono B P.left.1 P.left.2 hF
    (isAlgebraicSpace_yoneda B P.left.1 P.left.2 _) _ hmono hlft
  have hsep := Space.isSeparated_of_mono B P.left.1 P.left.2 _ hmono
  have hrep : F.IsRepresentable :=
    Space.isRepresentable_of_locallyQuasiFinite_separated B P.left.1 P.left.2 F _ hF
      (isAlgebraicSpace_yoneda B P.left.1 P.left.2 _) _ inferInstance hlqf hsep
  let Zo := F.reprX
  let e : yoneda.obj Zo ≅ F := F.reprW
  let ι : Zo.left.1 ⟶ Vs.obj P := B.inclusion.map Zo.hom
  -- a morphism into `Zo` over the base exists exactly on the support
  have hrepr (T : BigFppfOver B P.left.1 P.left.2) :
      Nonempty (T ⟶ Zo) ↔ Nonempty (F.obj (op T)) :=
    ⟨fun ⟨m⟩ => ⟨e.hom.app (op T) m⟩, fun ⟨m⟩ => ⟨e.inv.app (op T) m⟩⟩
  refine ⟨Zo.left.1, ι, ?_, ?_, Zo.left.2, ?_⟩
  · -- `ι` is a monomorphism: the two projections of `Z ×_U Z` agree
    have hsub : ∀ T : BigFppfOver B P.left.1 P.left.2, Subsingleton (T ⟶ Zo) := fun T =>
      ⟨fun m m' => by
        have := (hFsub (op T)).elim (e.hom.app (op T) m) (e.hom.app (op T) m')
        have h := congrArg (e.inv.app (op T)) this
        simpa using h⟩
    have hPc : B.Contains (pullback ι ι) :=
      Scheme.size_pullback_lt ι ι Zo.left.2 Zo.left.2
    let T₀ : BigFppfOver B P.left.1 P.left.2 :=
      Over.mk (ObjectProperty.homMk (X := B.obj hPc) (Y := B.obj P.left.2)
        (pullback.fst ι ι ≫ ι))
    let m₁ : T₀ ⟶ Zo := Over.homMk (ObjectProperty.homMk (pullback.fst ι ι)) (by
      apply ObjectProperty.hom_ext; rfl)
    let m₂ : T₀ ⟶ Zo := Over.homMk (ObjectProperty.homMk (pullback.snd ι ι)) (by
      apply ObjectProperty.hom_ext; exact pullback.condition.symm)
    have h12 : pullback.fst ι ι = pullback.snd ι ι :=
      congrArg (fun m : T₀ ⟶ Zo => B.inclusion.map m.left) ((hsub T₀).elim m₁ m₂)
    exact (mono_iff_fst_eq_snd (pullbackIsPullback ι ι)).mpr h12
  · -- `ι` is locally of finite type
    have h : Space.IsLocallyOfFiniteType B P.left.1 P.left.2
        (yoneda.map (Over.homMk Zo.hom (by simp) : Zo ⟶ Over.mk (𝟙 (B.obj P.left.2)))) := by
      have heq : yoneda.map (Over.homMk Zo.hom (by simp) :
          Zo ⟶ Over.mk (𝟙 (B.obj P.left.2))) =
          e.hom ≫ Space.toYonedaId B P.left.1 P.left.2 F := by
        ext T m
        apply Over.OverMorphism.ext
        show m.left ≫ Zo.hom = T.unop.hom
        exact Over.w m
      rw [heq]
      have := Space.isLocallyOfFiniteType_respectsIso B P.left.1 P.left.2
      exact MorphismProperty.RespectsIso.precomp _ e.hom _ hlft
    exact (Space.isLocallyOfFiniteType_yoneda_map_iff B P.left.1 P.left.2 _).mp h
  · intro a c
    -- the object of the site of `U` given by `c`
    let T : BigFppfOver B P.left.1 P.left.2 := Over.mk (𝒳.val.p.map c).left
    have hTa : (Over.map P.hom).obj T = 𝒳.val.p.obj a := congrArg Over.mk (Over.w (𝒳.val.p.map c))
    have hgT : 𝒳.val.p.map c = eqToHom hTa.symm ≫ g T := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, Over.eqToHom_left, eqToHom_refl, Category.id_comp]
      rfl
    have := hπa T
    have : 𝒳.val.p.IsStronglyCartesian (g T) (π T).a := hp.isStronglyCartesian_homLift _ _
    let c' : a ⟶ pt.x := c
    have : 𝒳.val.p.IsHomLift (𝒳.val.p.map c) c' := IsHomLift.map _ c
    obtain ⟨v, hvl, hv⟩ : ∃ v : a ⟶ (Y.obj T).x,
        𝒳.val.p.IsHomLift (eqToHom hTa.symm) v ∧ v ≫ (π T).a = c' :=
      ⟨Functor.IsStronglyCartesian.map 𝒳.val.p (g T) (π T).a hgT c', inferInstance,
        Functor.IsStronglyCartesian.fac 𝒳.val.p (g T) (π T).a hgT c'⟩
    have : IsIso v := by
      have := hvl
      exact isIso_of_isHomLift_of_isIso 𝒳.val.p hp (eqToHom hTa.symm) v
    have hcθ : c ≫ θ = c ↔ (π T).a ≫ θ = (π T).a := by
      have h := comp_eq_self_iff_of_isIso v (π T).a θ
      rw [hv] at h
      exact h
    rw [hcθ, ← hsupp T, ← hrepr T]
    constructor
    · rintro ⟨g', hg'⟩
      exact ⟨Over.homMk (ObjectProperty.homMk g') (by
        apply ObjectProperty.hom_ext
        exact hg')⟩
    · rintro ⟨m⟩
      refine ⟨B.inclusion.map m.left, ?_⟩
      rw [← B.inclusion.map_comp]
      exact congrArg B.inclusion.map (Over.w m)

end AlgebraicGeometry.Stack

end
