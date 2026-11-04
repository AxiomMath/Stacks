module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafCoproduct

/-!
# Coproducts of sheaves on a big fppf site are universal

Let `P` be a coproduct of a family of sheaves of sets `F i` on the big fppf site over a scheme
`S`, presented by a colimit cofan with legs `ι i`. This file proves that the coproduct is
*universal* on representable test objects: a section `x` of `P` over an object `W` of the site
decomposes `W` into a family of pairwise disjoint open subobjects `W' i` which cover `W`, such
that the restriction of `x` to `W' i` comes from `F i`, and such that each `W' i` is universal
with that property. It also glues a family of charts of the members into a single chart of the
coproduct.

## Main results

* `CategoryTheory.Sheaf.injective_app_of_mono`: a monomorphism of sheaves of sets on a
  subcanonical site is injective on sections.
* `AlgebraicGeometry.BigFppfSite.exists_mem_arrows_mem_range` and
  `AlgebraicGeometry.BigFppfOver.exists_mem_arrows_mem_range`: every covering sieve of a big
  fppf site, and of the big fppf site over `S`, is jointly surjective on points.
* `AlgebraicGeometry.Sheaf.exists_isOpenImmersion_piece_of_isColimit_cofan`: the open
  subobject of `W` on which a section of the coproduct comes from the `i₀`-th member, together
  with its universal property.
* `AlgebraicGeometry.Sheaf.exists_clopen_decomposition_of_isColimit_cofan`: the resulting
  decomposition of `W` into pairwise disjoint open subobjects covering `W`.
* `AlgebraicGeometry.exists_hom_yoneda_of_isColimit_cofan`: charts `yoneda.obj (U i) ⟶ F i` of
  the members glue to a chart `yoneda.obj V ⟶ P` of the coproduct, as soon as `V` is the
  coproduct of the `U i` inside the site.

## References

* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
* [Stacks Project, Tag 0F15](https://stacks.math.columbia.edu/tag/0F15)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ u

namespace CategoryTheory

/-! ### Monomorphisms of sheaves of sets on a subcanonical site are injective -/

/-- A monomorphism of sheaves of sets on a subcanonical site is injective on sections. -/
lemma Sheaf.injective_app_of_mono {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} [J.Subcanonical] {F G : Sheaf J (Type v₁)} (f : F ⟶ G)
    [Mono f] (W : C) : Function.Injective (f.hom.app (Opposite.op W)) := by
  intro s t hst
  let Y : Sheaf J (Type v₁) := ⟨yoneda.obj W,
    (isSheaf_iff_isSheaf_of_type J _).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)⟩
  have h1 : (ObjectProperty.homMk (yonedaEquiv.symm s) : Y ⟶ F) ≫ f
      = (ObjectProperty.homMk (yonedaEquiv.symm t) : Y ⟶ F) ≫ f := by
    refine Sheaf.hom_ext (?_ : yonedaEquiv.symm s ≫ f.hom = yonedaEquiv.symm t ≫ f.hom)
    refine yonedaEquiv.injective ?_
    rwa [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact yonedaEquiv.symm.injective (Sheaf.hom_ext_iff.1 ((cancel_mono f).1 h1))

end CategoryTheory

namespace AlgebraicGeometry

/-! ### Covering sieves of a big fppf site are jointly surjective on points -/

/-- The chosen covering families of a big fppf site are jointly surjective on points. -/
lemma BigFppfSite.exists_mem_range_of_mem_precoverage (B : BigFppfSite.{u}) {X : B.Schemes}
    {R : Presieve X} (hR : R ∈ B.precoverage X) (x : B.inclusion.obj X) :
    ∃ (Y : B.Schemes) (f : Y ⟶ X), R f ∧ x ∈ Set.range (B.inclusion.map f) := by
  obtain ⟨E, rfl, hE⟩ := hR
  have h1 : Presieve.ofArrows (fun i => B.inclusion.obj (E.X i))
      (fun i => B.inclusion.map (E.f i)) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj X) := by
    have h2 := B.isFppfCovering_of_isCovering hE
    rw [IsFppfCovering, Precoverage.mem_comap_iff] at h2
    rwa [PreZeroHypercover.presieve₀, Presieve.map_ofArrows] at h2
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at h1
  obtain ⟨i, hi⟩ := h1.1 x
  exact ⟨E.X i, E.f i, ⟨i⟩, hi⟩

/-- Every covering sieve of a big fppf site is jointly surjective on points: each point of the
target is in the image of one of the members of the sieve. -/
theorem BigFppfSite.exists_mem_arrows_mem_range (B : BigFppfSite.{u}) {X : B.Schemes}
    {R : Sieve X} (hR : R ∈ B.topology X) :
    ∀ x : B.inclusion.obj X,
      ∃ (Y : B.Schemes) (f : Y ⟶ X), R.arrows f ∧ x ∈ Set.range (B.inclusion.map f) := by
  rw [Precoverage.mem_toGrothendieck_iff] at hR
  induction hR with
  | of X R hR =>
      intro x
      obtain ⟨Y, f, hf, hx⟩ := B.exists_mem_range_of_mem_precoverage hR x
      exact ⟨Y, f, ⟨Y, 𝟙 Y, f, hf, by simp⟩, hx⟩
  | top X => exact fun x => ⟨X, 𝟙 X, trivial, by simp⟩
  | pullback X S _ Y f ih =>
      intro y
      obtain ⟨Z, g, hg, z, hz⟩ := ih (B.inclusion.map f y)
      obtain ⟨p, hp₁, hp₂⟩ := Scheme.exists_preimage_of_isPullback
        ((IsPullback.of_hasPullback f g).map B.inclusion) y z hz.symm
      exact ⟨Limits.pullback f g, Limits.pullback.fst f g,
        by simpa [Limits.pullback.condition] using S.downward_closed hg (pullback.snd f g),
        p, hp₁⟩
  | transitive X S R _ _ ih₁ ih₂ =>
      intro x
      obtain ⟨Z, g, hg, z, hz⟩ := ih₁ x
      obtain ⟨W, h, hh, w, hw⟩ := ih₂ hg z
      refine ⟨W, h ≫ g, hh, w, ?_⟩
      rw [B.inclusion.map_comp, Scheme.Hom.comp_apply, hw, hz]

/-- Every covering sieve of the big fppf site over `S` is jointly surjective on points. -/
theorem BigFppfOver.exists_mem_arrows_mem_range (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X : BigFppfOver B S hS} {R : Sieve X}
    (hR : R ∈ BigFppfOver.topology B S hS X) (x : (BigFppfOver.toScheme B S hS).obj X) :
    ∃ (Y : BigFppfOver B S hS) (f : Y ⟶ X), R.arrows f ∧
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map f) := by
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨Y, f, hf, hx⟩ := B.exists_mem_arrows_mem_range hR x
  exact ⟨Over.mk (f ≫ X.hom), Over.homMk f, (Sieve.overEquiv_iff R f).1 hf, hx⟩

/-! ### A section of a coproduct of sheaves lives on a clopen decomposition -/

section Decomposition

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Let `P` be a coproduct of sheaves `F i` on the big fppf site over `S`, with legs `ι i`, and
let `x` be a section of `P` over `W`. For every index `i₀` there is an open subobject `W₀ ⟶ W`
over which `x` is in the image of `ι i₀`, through which every `T ⟶ W` with that property
factors. -/
theorem Sheaf.exists_isOpenImmersion_piece_of_isColimit_cofan {I : Type w}
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (W : BigFppfOver B S hS) (x : P.obj.obj (op W)) (i₀ : I) :
    ∃ (W₀ : BigFppfOver B S hS) (p : W₀ ⟶ W),
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map p) ∧
      (∃ z : (F i₀).obj.obj (op W₀), (ι i₀).hom.app (op W₀) z = P.obj.map p.op x) ∧
      ∀ (T : BigFppfOver B S hS) (t : T ⟶ W),
        (∃ z : (F i₀).obj.obj (op T), (ι i₀).hom.app (op T) z = P.obj.map t.op x) →
        ∃ t' : T ⟶ W₀, t' ≫ p = t := by
  classical
  have hΩ : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (yoneda.obj ((⊤_ (BigFppfOver B S hS)) ⨿ (⊤_ (BigFppfOver B S hS)))) :=
    BigFppfOver.isSheaf_yoneda_obj B S hS _
  set Y : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨_, hΩ⟩
  set κ : ∀ i, F i ⟶ Y := fun i => ObjectProperty.homMk
    (Presheaf.constToYoneda (F i).obj
      (if i = i₀ then (coprod.inl : ⊤_ (BigFppfOver B S hS) ⟶ _) else coprod.inr))
  set χ := Cofan.IsColimit.desc hP κ
  have key : ∀ (i : I) (T : BigFppfOver B S hS) (z : (F i).obj.obj (op T)),
      χ.hom.app (op T) ((ι i).hom.app (op T) z)
        = terminal.from T ≫
          (if i = i₀ then (coprod.inl : ⊤_ (BigFppfOver B S hS) ⟶ _) else coprod.inr) :=
    fun i T z => congrArg (fun m : F i ⟶ Y => m.hom.app (op T) z)
      (Limits.comp_cofan_isColimit_desc hP κ i)
  have hnat : ∀ (T T' : BigFppfOver B S hS) (t : T ⟶ T') (y : P.obj.obj (op T')),
      χ.hom.app (op T) (P.obj.map t.op y) = t ≫ χ.hom.app (op T') y :=
    fun T T' t y => NatTrans.naturality_apply χ.hom t.op y
  have hinl : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (coprod.inl : ⊤_ (BigFppfOver B S hS) ⟶ _)) :=
    isOpenImmersion_left_of_isColimit_binaryCofan
      (isColimitBinaryCofanToSchemeMap (B := B) (hS := hS) (⊤_ _) (⊤_ _))
  set c := χ.hom.app (op W) x
  set W₀ := Limits.pullback c (coprod.inl : ⊤_ (BigFppfOver B S hS) ⟶ _)
  set p : W₀ ⟶ W := Limits.pullback.fst c (coprod.inl : ⊤_ (BigFppfOver B S hS) ⟶ _) with hpdef
  refine ⟨W₀, p, ?_, ?_, ?_⟩
  · rw [hpdef, ← PreservesPullback.iso_hom_fst (BigFppfOver.toScheme B S hS) c
      (coprod.inl : ⊤_ (BigFppfOver B S hS) ⟶ _)]
    exact IsOpenImmersion.comp _ _
  · have hFsheaf : Presieve.IsSheaf (BigFppfOver.topology B S hS) (F i₀).obj :=
      (isSheaf_iff_isSheaf_of_type _ _).1 (F i₀).property
    have hPsheaf : Presieve.IsSheaf (BigFppfOver.topology B S hS) P.obj :=
      (isSheaf_iff_isSheaf_of_type _ _).1 P.property
    have hmono : Mono (ι i₀) := Sheaf.mono_cofan_inj_bigFppfOver ι hP i₀
    have hinj : ∀ T : BigFppfOver B S hS, Function.Injective ((ι i₀).hom.app (op T)) :=
      fun T => CategoryTheory.Sheaf.injective_app_of_mono (ι i₀) T
    have hχx₀ : χ.hom.app (op W₀) (P.obj.map p.op x)
        = Limits.pullback.snd c (coprod.inl : ⊤_ (BigFppfOver B S hS) ⟶ _) ≫ coprod.inl := by
      rw [hnat W₀ W p x]
      exact Limits.pullback.condition
    set R : Sieve W₀ :=
      { arrows := fun T t => ∃ z : (F i₀).obj.obj (op T),
          (ι i₀).hom.app (op T) z = P.obj.map t.op (P.obj.map p.op x)
        downward_closed := by
          rintro T T' t ⟨z, hz⟩ u
          refine ⟨(F i₀).obj.map u.op z, ?_⟩
          rw [NatTrans.naturality_apply (ι i₀).hom u.op z, hz, ← Functor.map_comp_apply,
            ← op_comp] }
    have hRmem : R ∈ BigFppfOver.topology B S hS W₀ := by
      refine (BigFppfOver.topology B S hS).superset_covering ?_
        (CategoryTheory.Sheaf.sieveOfSection_iSup_range_mem (BigFppfOver.topology B S hS) ι hP
          (op W₀) (P.obj.map p.op x))
      intro T t ht
      have ht' : P.obj.map t.op (P.obj.map p.op x) ∈
          (⨆ i, Subfunctor.range (ι i).hom).obj (op T) := ht
      rw [Subfunctor.iSup_obj, Set.mem_iUnion] at ht'
      obtain ⟨i, z, hz⟩ := ht'
      by_cases hi : i = i₀
      · subst hi
        exact ⟨z, hz⟩
      · have hempty : IsEmpty ((BigFppfOver.toScheme B S hS).obj T) := by
          refine ⟨fun y => ?_⟩
          have h1 : χ.hom.app (op T) (P.obj.map t.op (P.obj.map p.op x))
              = terminal.from T ≫ (coprod.inr : ⊤_ (BigFppfOver B S hS) ⟶ _) := by
            rw [← hz, key i T z, if_neg hi]
          have h2 : χ.hom.app (op T) (P.obj.map t.op (P.obj.map p.op x))
              = (t ≫ Limits.pullback.snd c (coprod.inl : ⊤_ (BigFppfOver B S hS) ⟶ _)) ≫
                coprod.inl := by
            rw [hnat T W₀ t (P.obj.map p.op x), hχx₀]
            simp
          have h3 := congrArg
            (fun m : (BigFppfOver.toScheme B S hS).obj T ⟶
              (BigFppfOver.toScheme B S hS).obj _ => m y)
            (congrArg (BigFppfOver.toScheme B S hS).map (h1.symm.trans h2))
          simp only [Functor.map_comp, Scheme.Hom.comp_apply] at h3
          exact ne_of_isColimit_binaryCofan
            (isColimitBinaryCofanToSchemeMap (B := B) (hS := hS) (⊤_ _) (⊤_ _)) _ _ h3.symm
        have hbot : (⊥ : Sieve T) ∈ BigFppfOver.topology B S hS T :=
          BigFppfOver.bot_mem_topology T hempty
        obtain ⟨z'⟩ := hFsheaf.nonempty_obj_of_bot_mem _ hbot
        exact ⟨z', (hPsheaf.subsingleton_obj_of_bot_mem _ hbot).elim _ _⟩
    have hchoice : ∀ (T : BigFppfOver B S hS) (t : T ⟶ W₀), R.arrows t →
        ∃ z : (F i₀).obj.obj (op T),
          (ι i₀).hom.app (op T) z = P.obj.map t.op (P.obj.map p.op x) := fun _ _ h => h
    choose zz hzz using hchoice
    set fam : Presieve.FamilyOfElements (F i₀).obj R.arrows :=
      fun T t ht => zz T t ht
    have hcompat : fam.Compatible := by
      rw [Presieve.compatible_iff_sieveCompatible]
      intro T T' t u ht
      refine hinj T' ?_
      rw [NatTrans.naturality_apply (ι i₀).hom u.op (zz T t ht), hzz T t ht,
        hzz T' (u ≫ t) (R.downward_closed ht u)]
      simp only [← Functor.map_comp_apply, ← op_comp, Category.assoc]
    obtain ⟨z, hz, -⟩ := hFsheaf R hRmem _ hcompat
    refine ⟨z, ((hPsheaf R hRmem).isSeparatedFor).ext fun {T} t ht => ?_⟩
    rw [← NatTrans.naturality_apply (ι i₀).hom t.op z, hz t ht]
    exact hzz T t ht
  · rintro T t ⟨z, hz⟩
    refine ⟨Limits.pullback.lift t (terminal.from T) ?_, Limits.pullback.lift_fst _ _ _⟩
    rw [← hnat T W t x, ← hz, key i₀ T z, if_pos rfl]

/-- A section `x` of a coproduct `P = ∐ F i` of sheaves over an object `W` of the big fppf site
over `S` decomposes `W` into pairwise disjoint open subobjects `W' i` covering `W`, such that
`x` restricted to `W' i` comes from `F i`, each `W' i` being universal with that property. -/
theorem Sheaf.exists_clopen_decomposition_of_isColimit_cofan {I : Type w}
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (W : BigFppfOver B S hS) (x : P.obj.obj (op W)) :
    ∃ (W' : I → BigFppfOver B S hS) (p : ∀ i, W' i ⟶ W),
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p i))) ∧
      (∀ i, ∃ z : (F i).obj.obj (op (W' i)),
        (ι i).hom.app (op (W' i)) z = P.obj.map (p i).op x) ∧
      (∀ i i', i ≠ i' → ∀ (y : (BigFppfOver.toScheme B S hS).obj (W' i))
        (y' : (BigFppfOver.toScheme B S hS).obj (W' i')),
        (BigFppfOver.toScheme B S hS).map (p i) y ≠
          (BigFppfOver.toScheme B S hS).map (p i') y') ∧
      (∀ w : (BigFppfOver.toScheme B S hS).obj W,
        ∃ i, w ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p i))) ∧
      (∀ (i : I) (T : BigFppfOver B S hS) (t : T ⟶ W),
        (∃ z : (F i).obj.obj (op T), (ι i).hom.app (op T) z = P.obj.map t.op x) →
        ∃ t' : T ⟶ W' i, t' ≫ p i = t) := by
  choose W' p hoi hsec huniv using fun i =>
    Sheaf.exists_isOpenImmersion_piece_of_isColimit_cofan ι hP W x i
  refine ⟨W', p, hoi, hsec, ?_, ?_, huniv⟩
  · intro i i' hii' y y' hyy'
    obtain ⟨z, hz⟩ := hsec i
    obtain ⟨z', hz'⟩ := hsec i'
    have hx : (ι i).hom.app (op (Limits.pullback (p i) (p i')))
          ((F i).obj.map (Limits.pullback.fst (p i) (p i')).op z)
        = (ι i').hom.app (op (Limits.pullback (p i) (p i')))
          ((F i').obj.map (Limits.pullback.snd (p i) (p i')).op z') := by
      rw [NatTrans.naturality_apply (ι i).hom (Limits.pullback.fst (p i) (p i')).op z,
        NatTrans.naturality_apply (ι i').hom (Limits.pullback.snd (p i) (p i')).op z', hz, hz']
      simp only [← Functor.map_comp_apply, ← op_comp, Limits.pullback.condition]
    have hempty := Sheaf.isEmpty_toScheme_of_eq_of_ne ι hP hii' _ _ hx
    obtain ⟨q, -, -⟩ := Scheme.exists_preimage_of_isPullback
      ((IsPullback.of_hasPullback (p i) (p i')).map (BigFppfOver.toScheme B S hS)) y y' hyy'
    exact hempty.false q
  · intro w
    obtain ⟨T, t, ht, y, hy⟩ := BigFppfOver.exists_mem_arrows_mem_range B S hS
      (CategoryTheory.Sheaf.sieveOfSection_iSup_range_mem
        (BigFppfOver.topology B S hS) ι hP (op W) x) w
    have ht' : P.obj.map t.op x ∈ (⨆ i, Subfunctor.range (ι i).hom).obj (op T) := ht
    rw [Subfunctor.iSup_obj, Set.mem_iUnion] at ht'
    obtain ⟨i, z, hz⟩ := ht'
    obtain ⟨t', ht'⟩ := huniv i T t ⟨z, hz⟩
    refine ⟨i, (BigFppfOver.toScheme B S hS).map t' y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ht', hy]

/-! ### The atlas morphism of a coproduct of algebraic spaces -/

/-- Let `P` be a coproduct of sheaves `F i` with legs `ι i`, and `V` a coproduct of objects
`U i` of the big fppf site over `S` with legs `j i`. Then morphisms `f i : yoneda.obj (U i) ⟶ F i`
glue to a morphism `v : yoneda.obj V ⟶ P` with `yoneda.map (j i) ≫ v = f i ≫ ι i`. -/
theorem exists_hom_yoneda_of_isColimit_cofan {I : Type w}
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, F i ⟶ P)
    {U : I → BigFppfOver B S hS} (f : ∀ i, yoneda.obj (U i) ⟶ (F i).obj)
    {V : BigFppfOver B S hS} {j : ∀ i, U i ⟶ V} (hV : IsColimit (Cofan.mk V j)) :
    ∃ v : yoneda.obj V ⟶ P.obj, ∀ i, yoneda.map (j i) ≫ v = f i ≫ (ι i).hom := by
  classical
  have hPsheaf : Presieve.IsSheaf (BigFppfOver.topology B S hS) P.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).1 P.property
  have hoi : ∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i)) := fun i =>
    isOpenImmersion_toScheme_map_cofan hV i
  have hjmono : ∀ i, Mono (j i) := fun i =>
    have := hoi i
    (BigFppfOver.toScheme B S hS).mono_of_mono_map (IsOpenImmersion.mono _)
  have hindep : ∀ (T : BigFppfOver B S hS) (i i' : I) (h : T ⟶ U i) (h' : T ⟶ U i'),
      h ≫ j i = h' ≫ j i' →
      (ι i).hom.app (op T) ((f i).app (op T) h)
        = (ι i').hom.app (op T) ((f i').app (op T) h') := by
    intro T i i' h h' hcomp
    by_cases hii' : i = i'
    · subst hii'
      have := hjmono i
      rw [(cancel_mono (j i)).1 hcomp]
    · have hempty : IsEmpty ((BigFppfOver.toScheme B S hS).obj T) := by
        refine ⟨fun y => ?_⟩
        have h1 := congrArg
          (fun m : (BigFppfOver.toScheme B S hS).obj T ⟶
            (BigFppfOver.toScheme B S hS).obj V => m y)
          (congrArg (BigFppfOver.toScheme B S hS).map hcomp)
        simp only [Functor.map_comp, Scheme.Hom.comp_apply] at h1
        exact ne_toScheme_map_cofan hV hii' _ _ h1
      have hbot : (⊥ : Sieve T) ∈ BigFppfOver.topology B S hS T :=
        BigFppfOver.bot_mem_topology T hempty
      exact (hPsheaf.subsingleton_obj_of_bot_mem _ hbot).elim _ _
  have hcov : Sieve.ofArrows U j ∈ BigFppfOver.topology B S hS V :=
    BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS j hoi fun w =>
      Set.mem_iUnion.1 ((iUnion_range_toScheme_map_cofan hV).symm ▸ Set.mem_univ w)
  have hchoice : ∀ (T : BigFppfOver B S hS) (g : T ⟶ V), (Sieve.ofArrows U j).arrows g →
      ∃ y : P.obj.obj (op T), ∀ (i : I) (h : T ⟶ U i), h ≫ j i = g →
        y = (ι i).hom.app (op T) ((f i).app (op T) h) := by
    rintro T g ⟨Z, h, e, ⟨i⟩, hcomp⟩
    exact ⟨(ι i).hom.app (op T) ((f i).app (op T) h),
      fun i' h' hh' => hindep T i i' h h' (hcomp.trans hh'.symm)⟩
  choose yy hyy using hchoice
  set fam : Presieve.FamilyOfElements P.obj (Sieve.ofArrows U j).arrows :=
    fun T g hg => yy T g hg with hfamdef
  have hcompat : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro T T' g u hg
    obtain ⟨Z, h, e, ⟨i⟩, hcomp⟩ := id hg
    simp only [hfamdef]
    rw [hyy T g hg i h hcomp,
      hyy T' (u ≫ g) ((Sieve.ofArrows U j).downward_closed hg u) i (u ≫ h)
        (by rw [Category.assoc, hcomp]),
      ← NatTrans.naturality_apply (ι i).hom u.op ((f i).app (op T) h)]
    exact congrArg ((ι i).hom.app (op T')) (NatTrans.naturality_apply (f i) u.op h)
  obtain ⟨γ, hγ, -⟩ := hPsheaf _ hcov fam hcompat
  refine ⟨yonedaEquiv.symm γ, fun i => yonedaEquiv.injective ?_⟩
  rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_apply]
  have h1 : (yonedaEquiv.symm γ).app (op (U i)) (j i) = P.obj.map (j i).op γ :=
    yonedaEquiv_symm_app_apply γ (op (U i)) (j i)
  rw [h1, hγ (j i) ⟨U i, 𝟙 (U i), j i, ⟨i⟩, Category.id_comp _⟩]
  simp only [hfamdef]
  exact hyy (U i) (j i) _ i (𝟙 (U i)) (Category.id_comp _)

end Decomposition

end AlgebraicGeometry

end

