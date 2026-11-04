module

public import StacksFrontier.AlgebraicGeometry.Limits.EtaleRelationDescent
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AtlasDiagram

/-!
# Étale morphisms to the limit of a presented system descend to a stage

## Main results

* `AlgebraicGeometry.Space.exists_etale_siteModel`: an étale, quasi-compact and quasi-separated
  morphism of objects of the big fppf site to the limit of a cofiltered system of objects of the
  site with affine transition morphisms, whose limit is realised in the site, is a base change of
  one to a stage.
* `AlgebraicGeometry.Space.isPullback_of_isPullback_toScheme`: a square of the big fppf site is
  cartesian as soon as its square of schemes is.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.hasPullbacks_bigFppfOver
  AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A square of the big fppf site of `S` is cartesian as soon as its square of underlying
schemes is.** The functor to schemes is faithful, preserves the fibre products of the site and
reflects isomorphisms. -/
theorem isPullback_of_isPullback_toScheme {P Q R W : BigFppfOver B S hS} {a : P ⟶ Q}
    {b : P ⟶ R} {c : Q ⟶ W} {e : R ⟶ W}
    (h : IsPullback ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b)
      ((BigFppfOver.toScheme B S hS).map c) ((BigFppfOver.toScheme B S hS).map e)) :
    IsPullback a b c e := by
  have _ : ReflectsLimit (cospan c e) (BigFppfOver.toScheme B S hS) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  exact IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) h

/-- A quasi-compact scheme with a morphism locally of finite type to an object of the big fppf
site of `S`, presented as an object of the site over that object. -/
noncomputable abbrev siteObjectOfLocallyOfFiniteType (T : BigFppfOver B S hS) {M : Scheme.{u}}
    (f : M ⟶ (BigFppfOver.toScheme B S hS).obj T) [LocallyOfFiniteType f] [CompactSpace M] :
    BigFppfOver B S hS :=
  Over.mk (X := B.obj hS) (Y := ⟨M, (Scheme.size_le_of_locallyOfFiniteType f).trans_lt
    T.left.property⟩) (ObjectProperty.homMk (f ≫ T.hom.hom))

/-- The morphism of the site underlying the morphism of finite type. -/
noncomputable abbrev siteObjectOfLocallyOfFiniteType.hom (T : BigFppfOver B S hS)
    {M : Scheme.{u}} (f : M ⟶ (BigFppfOver.toScheme B S hS).obj T) [LocallyOfFiniteType f]
    [CompactSpace M] : siteObjectOfLocallyOfFiniteType T f ⟶ T :=
  Over.homMk (ObjectProperty.homMk f) rfl

/-- The morphism of schemes underlying `siteObjectOfLocallyOfFiniteType.hom T f` is `f`. -/
@[simp]
theorem siteObjectOfLocallyOfFiniteType.toScheme_map_hom (T : BigFppfOver B S hS)
    {M : Scheme.{u}} (f : M ⟶ (BigFppfOver.toScheme B S hS).obj T) [LocallyOfFiniteType f]
    [CompactSpace M] :
    (BigFppfOver.toScheme B S hS).map (siteObjectOfLocallyOfFiniteType.hom T f) = f := rfl

/-- A morphism of schemes into the scheme of an object of the site, as a morphism of the site,
when its source is the scheme of an object of the site lying over it. -/
noncomputable abbrev siteObjectOfLocallyOfFiniteType.lift (T : BigFppfOver B S hS)
    {M : Scheme.{u}} (f : M ⟶ (BigFppfOver.toScheme B S hS).obj T) [LocallyOfFiniteType f]
    [CompactSpace M] {P : BigFppfOver B S hS} (g : (BigFppfOver.toScheme B S hS).obj P ⟶ M)
    (hg : P.hom.hom = g ≫ f ≫ T.hom.hom) :
    P ⟶ siteObjectOfLocallyOfFiniteType T f :=
  Over.homMk (ObjectProperty.homMk g) (by
    ext1
    exact hg.symm.trans rfl)

/-- The morphism of schemes underlying `siteObjectOfLocallyOfFiniteType.lift T f g hg` is `g`. -/
@[simp]
theorem siteObjectOfLocallyOfFiniteType.toScheme_map_lift (T : BigFppfOver B S hS)
    {M : Scheme.{u}} (f : M ⟶ (BigFppfOver.toScheme B S hS).obj T) [LocallyOfFiniteType f]
    [CompactSpace M] {P : BigFppfOver B S hS} (g : (BigFppfOver.toScheme B S hS).obj P ⟶ M)
    (hg : P.hom.hom = g ≫ f ≫ T.hom.hom) :
    (BigFppfOver.toScheme B S hS).map (siteObjectOfLocallyOfFiniteType.lift T f g hg) = g := rfl

/-- **An étale morphism to the limit of a system of objects of the site descends to a stage.**
Let `D` be a cofiltered system of quasi-compact and quasi-separated objects of the big fppf site
with affine transition morphisms, whose limit `c` is realised in the site. An étale,
quasi-compact and quasi-separated morphism `p' : M' ⟶ c.pt` of the site is the base change of an
étale, quasi-compact and quasi-separated morphism to a stage. -/
theorem exists_etale_siteModel {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigFppfOver B S hS)
    (hAff : ∀ {i j : I} (e : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (D.map e)))
    (hqc : ∀ i, CompactSpace ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    (hqs : ∀ i, QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    {c : Cone D} (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    {M' : BigFppfOver B S hS} (p' : M' ⟶ c.pt)
    (het : Etale ((BigFppfOver.toScheme B S hS).map p'))
    (hqc' : QuasiCompact ((BigFppfOver.toScheme B S hS).map p'))
    (hqs' : QuasiSeparated ((BigFppfOver.toScheme B S hS).map p')) :
    ∃ (i : I) (M : BigFppfOver B S hS) (p : M ⟶ D.obj i) (m : M' ⟶ M),
      Etale ((BigFppfOver.toScheme B S hS).map p) ∧
      QuasiCompact ((BigFppfOver.toScheme B S hS).map p) ∧
      QuasiSeparated ((BigFppfOver.toScheme B S hS).map p) ∧ IsPullback m p' p (c.π.app i) := by
  let T := BigFppfOver.toScheme B S hS
  have : ∀ {i j : I} (e : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom ((D ⋙ T).map e) := hAff
  have : ∀ i, CompactSpace ((D ⋙ T).obj i) := hqc
  have : ∀ i, QuasiSeparatedSpace ((D ⋙ T).obj i) := hqs
  obtain ⟨i, M₀, p₀, m₀, het₀, hqc₀, hqs₀, hpb⟩ :=
    Scheme.exists_etale_isPullback_of_isLimit (D ⋙ T) (T.mapCone c) hc (T.map p')
  have : CompactSpace M₀ := @QuasiCompact.compactSpace_of_compactSpace _ _ p₀ hqc₀ (hqc i)
  have : LocallyOfFiniteType p₀ := inferInstance
  have hw : M'.hom.hom = m₀ ≫ p₀ ≫ (D.obj i).hom.hom := by
    have h₁ : (T.map p') ≫ c.pt.hom.hom = M'.hom.hom := congrArg (fun f => f.hom) (Over.w p')
    have h₂ : T.map (c.π.app i) ≫ (D.obj i).hom.hom = c.pt.hom.hom :=
      congrArg (fun f => f.hom) (Over.w (c.π.app i))
    rw [← h₁, ← h₂, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ (D.obj i).hom.hom) hpb.w.symm
  exact ⟨i, siteObjectOfLocallyOfFiniteType (D.obj i) p₀,
    siteObjectOfLocallyOfFiniteType.hom (D.obj i) p₀,
    siteObjectOfLocallyOfFiniteType.lift (D.obj i) p₀ m₀ hw, het₀, hqc₀, hqs₀,
    isPullback_of_isPullback_toScheme hpb⟩

section Stage

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigFppfOver B S hS)
  (hAff : ∀ {i j : I} (e : i ⟶ j),
    _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (D.map e)))
  (hqc : ∀ i, CompactSpace ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
  (hqs : ∀ i, QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
  {c : Cone D} (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))

include hAff hqc hqs hc in
/-- **Stacks 01ZC, injectivity, for objects of the site over a stage.** Two morphisms over a
stage `D i`, from a quasi-compact object `X` to an object `Y` locally of finite type over
`D i`, which agree on the base change of `X` to the limit agree on its base change to a later
stage, whatever cartesian square is used to present that base change. -/
theorem exists_stage_eq_of_isPullback {i : I} {X Y : BigFppfOver B S hS} (x : X ⟶ D.obj i)
    (hX : CompactSpace ((BigFppfOver.toScheme B S hS).obj X)) (y : Y ⟶ D.obj i)
    (hy : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map y)) (u v : X ⟶ Y)
    (hu : u ≫ y = x) (hv : v ≫ y = x) {P : BigFppfOver B S hS} {a : P ⟶ X} {b : P ⟶ c.pt}
    (hP : IsPullback a b x (c.π.app i)) (h : a ≫ u = a ≫ v) :
    ∃ (j : I) (e : j ⟶ i), ∀ {P' : BigFppfOver B S hS} {a' : P' ⟶ X} {b' : P' ⟶ D.obj j},
      IsPullback a' b' x (D.map e) → a' ≫ u = a' ≫ v := by
  let T := BigFppfOver.toScheme B S hS
  have : ∀ {i j : I} (e : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom ((D ⋙ T).map e) := hAff
  have : ∀ i, CompactSpace ((D ⋙ T).obj i) := hqc
  have : ∀ i, QuasiSeparatedSpace ((D ⋙ T).obj i) := hqs
  have : CompactSpace (Over.mk (T.map x)).left := hX
  have : LocallyOfFiniteType (T.map y) := hy
  let hPT := (hP.map T).flip
  obtain ⟨j, e, hj⟩ := Scheme.exists_stage_eq_of_baseChange (D ⋙ T) (T.mapCone c) hc i
    (Over.mk (T.map x)) (T.map y) (T.map u) (T.map v)
    (by rw [← T.map_comp, hu]; rfl) (by rw [← T.map_comp, hv]; rfl) (by
      change pullback.snd (T.map (c.π.app i)) (T.map x) ≫ T.map u =
        pullback.snd (T.map (c.π.app i)) (T.map x) ≫ T.map v
      rw [← hPT.isoPullback_inv_snd, Category.assoc, Category.assoc, ← T.map_comp,
        ← T.map_comp, h])
  refine ⟨j, e, fun {P' a' b'} hP' => T.map_injective ?_⟩
  let hP'T := (hP'.map T).flip
  change pullback.snd (T.map (D.map e)) (T.map x) ≫ T.map u =
    pullback.snd (T.map (D.map e)) (T.map x) ≫ T.map v at hj
  rw [T.map_comp, T.map_comp, ← hP'T.isoPullback_hom_snd, Category.assoc, Category.assoc, hj]

include hAff hqc hqs hc in
/-- **Stacks 01ZC, surjectivity, for objects of the site over a stage.** A morphism over a stage
`D i`, from the base change to the limit of a quasi-compact and quasi-separated object `X` over
`D i` to an object `Y` locally of finite presentation over `D i`, comes from a morphism on the
base change of `X` to a later stage, whatever cartesian square is used to present that base
change. -/
theorem exists_stage_hom_of_isPullback {i : I} {X Y : BigFppfOver B S hS} (x : X ⟶ D.obj i)
    (hX : CompactSpace ((BigFppfOver.toScheme B S hS).obj X))
    (hX' : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj X)) (y : Y ⟶ D.obj i)
    (hy : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map y))
    {P : BigFppfOver B S hS} {a : P ⟶ X} {b : P ⟶ c.pt}
    (hP : IsPullback a b x (c.π.app i)) (g : P ⟶ Y) (hg : g ≫ y = a ≫ x) :
    ∃ (j : I) (e : j ⟶ i), ∀ {P' : BigFppfOver B S hS} {a' : P' ⟶ X} {b' : P' ⟶ D.obj j}
      (hP' : IsPullback a' b' x (D.map e)), ∃ g' : P' ⟶ Y, g' ≫ y = a' ≫ x ∧
        hP'.lift a (b ≫ c.π.app j) (by rw [Category.assoc, c.w, hP.w]) ≫ g' = g := by
  let T := BigFppfOver.toScheme B S hS
  have : ∀ {i j : I} (e : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom ((D ⋙ T).map e) := hAff
  have : ∀ i, CompactSpace ((D ⋙ T).obj i) := hqc
  have : ∀ i, QuasiSeparatedSpace ((D ⋙ T).obj i) := hqs
  have : CompactSpace (Over.mk (T.map x)).left := hX
  have : QuasiSeparatedSpace (Over.mk (T.map x)).left := hX'
  have : LocallyOfFinitePresentation (T.map y) := hy
  let hPT := (hP.map T).flip
  obtain ⟨j, g₀, hg₀, hg₀'⟩ := Scheme.exists_stage_hom_of_baseChange (D ⋙ T) (T.mapCone c) hc i
    (Over.mk (T.map x)) (T.map y) (hPT.isoPullback.inv ≫ T.map g) (by
      change (hPT.isoPullback.inv ≫ T.map g) ≫ T.map y =
        pullback.snd (T.map (c.π.app i)) (T.map x) ≫ T.map x
      rw [Category.assoc, ← T.map_comp, hg, T.map_comp, ← Category.assoc,
        hPT.isoPullback_inv_snd])
  refine ⟨j.left, j.hom, fun {P' a' b'} hP' => ?_⟩
  have hP'w : T.map b' ≫ T.map (D.map j.hom) = T.map a' ≫ T.map x := by
    rw [← T.map_comp, ← T.map_comp, hP'.w]
  let φ' : T.obj P' ⟶ pullback (T.map (D.map j.hom)) (T.map x) :=
    pullback.lift (T.map b') (T.map a') hP'w
  let g' : T.obj P' ⟶ T.obj Y := φ' ≫ g₀
  have hg' : g' ≫ T.map y = T.map a' ≫ T.map x := by
    change (φ' ≫ g₀) ≫ T.map y = _
    rw [Category.assoc, hg₀]
    change φ' ≫ pullback.snd (T.map (D.map j.hom)) (T.map x) ≫ T.map x = _
    rw [pullback.lift_snd_assoc]
  let G : P' ⟶ Y := Over.homMk (ObjectProperty.homMk g') (by
    ext1
    change g' ≫ Y.hom.hom = P'.hom.hom
    have h₁ : T.map y ≫ (D.obj i).hom.hom = Y.hom.hom := congrArg (fun f => f.hom) (Over.w y)
    have h₂ : T.map x ≫ (D.obj i).hom.hom = X.hom.hom := congrArg (fun f => f.hom) (Over.w x)
    have h₃ : T.map a' ≫ X.hom.hom = P'.hom.hom := congrArg (fun f => f.hom) (Over.w a')
    rw [← h₁, ← Category.assoc, hg', Category.assoc, h₂, h₃])
  have hGT : T.map G = g' := rfl
  refine ⟨G, T.map_injective (by rw [T.map_comp, T.map_comp, hGT, hg']), T.map_injective ?_⟩
  rw [T.map_comp, hGT]
  let ψ : T.obj P ⟶ pullback (T.map (c.π.app i)) (T.map x) :=
    pullback.lift (T.map b) (T.map a) (by rw [← T.map_comp, ← T.map_comp, hP.w])
  have hψ : ψ ≫ hPT.isoPullback.inv = 𝟙 _ := by
    apply hPT.hom_ext
    · rw [Category.assoc, hPT.isoPullback_inv_fst, Category.id_comp]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc, hPT.isoPullback_inv_snd, Category.id_comp]
      exact pullback.lift_snd _ _ _
  have hcomp : T.map (hP'.lift a (b ≫ c.π.app j.left) (by rw [Category.assoc, c.w, hP.w])) ≫
      φ' = ψ ≫ _root_.AlgebraicGeometry.baseChangeTransition
        (T.map (D.map j.hom)) (T.map (c.π.app i)) (T.map (c.π.app j.left))
        (by rw [← T.map_comp, c.w]) (Over.mk (T.map x)) := by
    apply pullback.hom_ext
    · simp only [φ', Category.assoc, pullback.lift_fst, ← T.map_comp, IsPullback.lift_snd]
      rw [T.map_comp]
      exact ((congrArg (ψ ≫ ·) (_root_.AlgebraicGeometry.baseChangeTransition_fst _ _ _ _
        (Over.mk (T.map x)))).trans (pullback.lift_fst_assoc _ _ _ _)).symm
    · simp only [φ', Category.assoc, pullback.lift_snd, ← T.map_comp, IsPullback.lift_fst]
      exact ((congrArg (ψ ≫ ·) (_root_.AlgebraicGeometry.baseChangeTransition_snd _ _ _ _
        (Over.mk (T.map x)))).trans (pullback.lift_snd _ _ _)).symm
  change T.map _ ≫ φ' ≫ g₀ = T.map g
  rw [← Category.assoc, hcomp, Category.assoc]
  change ψ ≫ (_root_.AlgebraicGeometry.baseChangeTransition (D ⋙ T |>.map j.hom)
    ((T.mapCone c).π.app i) ((T.mapCone c).π.app j.left) ((T.mapCone c).w j.hom)
    (Over.mk (T.map x)) ≫ g₀) = _
  rw [hg₀', ← Category.assoc, hψ, Category.id_comp]

end Stage

end AlgebraicGeometry.Space

end
