module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact

/-!
# Finite coproducts of quasi-compact sheaves

Stacks tag 0GMQ (Lemma 7.17.6). An object `F` of the topos `Sh(C)` of sheaves of sets is
quasi-compact when every epimorphism `∐_{i ∈ I} F_i ⟶ F` restricts along some finite `S ⊆ I` to
an epimorphism `∐_{i ∈ S} F_i ⟶ F`. For `n ≥ 1`, a coproduct of `n` quasi-compact sheaves is
quasi-compact. The binary case rests on two structural facts about `Sh(C)`, both proved here:
arbitrary coproducts are universal colimits, and epimorphisms are stable under base change.

The predicate used here phrases surjectivity as `CategoryTheory.Epi` and the finite subset as a
`Finset`. `CategoryTheory.Sheaf.IsQuasiCompact` phrases the same definition with
`CategoryTheory.Sheaf.IsLocallySurjective` and a finite `Set`;
`Sheaf.quasiCompact_iff_isQuasiCompact` identifies the two, so the lemma proved here also
applies to the other spelling, for instance to the hypothesis of Stacks 0GMR part (4).

## Main definitions

* `Sheaf.QuasiCompact`: quasi-compactness of an object of `Sh(C)`.

## Main results

* `Sheaf.coproduct_isUniversalColimit`: arbitrary coproducts in `Sh(C)` are universal colimits.
* `Sheaf.epi_pullback_snd`: epimorphisms in `Sh(C)` are stable under base change.
* `Sheaf.QuasiCompact.binaryCoproduct`: a binary coproduct of quasi-compact sheaves is
  quasi-compact.
* `Sheaf.quasiCompact_coproduct_fin`: a coproduct of `n ≥ 1` quasi-compact sheaves is
  quasi-compact.
* `Sheaf.quasiCompact_iff_isQuasiCompact`: the two spellings of quasi-compactness agree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **Quasi-compact object of the topos `Sh(C)`** (Stacks Tag 0D07, Definition 7.17.4).

An object `F` of `Sh(C)` is quasi-compact if for every index type `I` and every family
`Fi : I → Sh(C)` admitting a coproduct, and every surjective (epimorphic) map
`φ : ∐ Fi ⟶ F`, there is a finite subset `S ⊆ I` for which the restricted map
`∐_{i ∈ S} Fi ⟶ F`, namely `Sigma.desc (fun j => Sigma.ι Fi j ≫ φ)`, is again surjective
(an epimorphism).

A *surjective map of sheaves* is, by Definition 1, exactly an epimorphism in `Sh(C)`,
i.e. `CategoryTheory.Epi`. -/
@[sga "4 IV 8.7", sga "4 IX 1.2", sga "4 VI 1.1" "special case", sga "6 II 2.1.1"]
def Sheaf.QuasiCompact (F : Sheaf J (Type max u v)) : Prop :=
  ∀ {I : Type max u v} (Fi : I → Sheaf J (Type max u v)) [HasCoproduct Fi]
    (φ : ∐ Fi ⟶ F), Epi φ →
    ∃ (S : Finset I), ∃ _ : HasCoproduct (fun j : S => Fi j.1),
      Epi (Sigma.desc (fun j : S => Sigma.ι Fi j.1 ≫ φ))

/-- **Quasi-compactness is invariant under isomorphism**: if `F ≅ G` in `Sh(C)` and `F` is
quasi-compact, then so is `G`. -/
theorem Sheaf.QuasiCompact.of_iso {F G : Sheaf J (Type max u v)} (e : F ≅ G)
    (hF : Sheaf.QuasiCompact F) : Sheaf.QuasiCompact G := by
  intro I Gi _ ψ hψ
  obtain ⟨S, hS, hdesc⟩ := hF Gi (ψ ≫ e.inv) (epi_comp ψ e.inv)
  refine ⟨S, hS, ?_⟩
  have hfac : Sigma.desc (fun j : S => Sigma.ι Gi j.1 ≫ ψ ≫ e.inv) =
      Sigma.desc (fun j : S => Sigma.ι Gi j.1 ≫ ψ) ≫ e.inv := by
    ext j
    simp
  rw [hfac] at hdesc
  simpa using epi_comp (Sigma.desc (fun j : S => Sigma.ι Gi j.1 ≫ ψ) ≫ e.inv) e.hom

/-- A colimit cocone over a discrete diagram of types is jointly surjective. -/
private theorem presheaf_coproduct_isUniversalColimit.jointSurj
    {I : Type w} (G : Discrete I ⥤ Type w) (a : Cocone G) (ha : IsColimit a) (y : a.pt) :
    ∃ (j : Discrete I) (x : G.obj j), a.ι.app j x = y :=
  Types.jointly_surjective_of_isColimit ha y

/-- The components of a colimit cocone over a discrete diagram of types are jointly injective with
disjoint images (the canonical map `Σ i, G i → a.pt` is injective). -/
private theorem presheaf_coproduct_isUniversalColimit.sigmaInj
    {I : Type w} (G : Discrete I ⥤ Type w) (a : Cocone G) (ha : IsColimit a)
    {i i' : I} {s : G.obj ⟨i⟩} {s' : G.obj ⟨i'⟩}
    (he : a.ι.app ⟨i⟩ s = a.ι.app ⟨i'⟩ s') : (⟨i, s⟩ : Σ j, G.obj ⟨j⟩) = ⟨i', s'⟩ := by
  classical
  let σ : Cocone G := Cocone.mk (Σ i, G.obj ⟨i⟩)
    { app := fun j => TypeCat.ofHom (fun x => ⟨j.as, x⟩)
      naturality := by
        intro X Y g; obtain ⟨X⟩ := X; obtain ⟨Y⟩ := Y; obtain ⟨⟨(rfl : X = Y)⟩⟩ := g
        apply ConcreteCategory.hom_ext; intro x; simp }
  have hfac : ∀ (i : I) (x : G.obj ⟨i⟩), ha.desc σ (a.ι.app ⟨i⟩ x) = ⟨i, x⟩ := by
    intro i x
    have := ConcreteCategory.congr_hom (ha.fac σ ⟨i⟩) x
    rwa [ConcreteCategory.comp_apply] at this
  have := congrArg (ha.desc σ) he
  rwa [hfac, hfac] at this

/-- Every colimit cocone over a discrete diagram of types is a universal colimit. -/
@[sga "4 I 3.3" "special case"]
private theorem presheaf_coproduct_isUniversalColimit.typeColimitUniversal
    {I : Type w} (G : Discrete I ⥤ Type w) (a : Cocone G)
    (ha : IsColimit a) : IsUniversalColimit a := by
  intro F' c' α f h hα hpb
  classical
  have key : ∀ (i : I),
      (∀ x₁ y₁ : F'.obj ⟨i⟩,
          c'.ι.app ⟨i⟩ x₁ = c'.ι.app ⟨i⟩ y₁ ∧ α.app ⟨i⟩ x₁ = α.app ⟨i⟩ y₁ → x₁ = y₁)
      ∧ (∀ (x₂ : c'.pt) (x₃ : G.obj ⟨i⟩), f x₂ = a.ι.app ⟨i⟩ x₃ →
            ∃ x₁, c'.ι.app ⟨i⟩ x₁ = x₂ ∧ α.app ⟨i⟩ x₁ = x₃) := by
    intro i
    have hp := hpb ⟨i⟩
    rw [Types.isPullback_iff] at hp
    exact hp.2
  have hnat : ∀ (i : I) (y : F'.obj ⟨i⟩), f (c'.ι.app ⟨i⟩ y) = a.ι.app ⟨i⟩ (α.app ⟨i⟩ y) := by
    intro i y
    have happ := congr_app h ⟨i⟩
    simp only [NatTrans.comp_app, Functor.const_obj_obj, Functor.const_map_app] at happ
    have := ConcreteCategory.congr_hom happ y
    simp only [types_comp_apply] at this
    exact this.symm
  have hex : ∀ p : c'.pt, ∃ (i : I) (x₁ : F'.obj ⟨i⟩), c'.ι.app ⟨i⟩ x₁ = p := by
    intro p
    obtain ⟨⟨i⟩, x, hx⟩ := presheaf_coproduct_isUniversalColimit.jointSurj G a ha (f p)
    obtain ⟨x₁, hx₁, -⟩ := (key i).2 p x hx.symm
    exact ⟨_, x₁, hx₁⟩
  have huniq : ∀ (i i' : I) (x₁ : F'.obj ⟨i⟩) (x₁' : F'.obj ⟨i'⟩),
      c'.ι.app ⟨i⟩ x₁ = c'.ι.app ⟨i'⟩ x₁' →
      ∀ (s : Cocone F'), s.ι.app ⟨i⟩ x₁ = s.ι.app ⟨i'⟩ x₁' := by
    intro i i' x₁ x₁' heq s
    have hai : a.ι.app ⟨i⟩ (α.app ⟨i⟩ x₁) = a.ι.app ⟨i'⟩ (α.app ⟨i'⟩ x₁') := by
      rw [← hnat i x₁, ← hnat i' x₁', heq]
    have hsig := presheaf_coproduct_isUniversalColimit.sigmaInj G a ha hai
    obtain ⟨rfl, hαe⟩ := Sigma.mk.inj_iff.1 hsig
    rw [(key i).1 x₁ x₁' ⟨heq, eq_of_heq hαe⟩]
  refine ⟨{ desc := fun s => TypeCat.ofHom
               (fun p => s.ι.app ⟨(hex p).choose⟩ (hex p).choose_spec.choose),
            fac := ?_, uniq := ?_ }⟩
  · intro s ⟨j⟩
    apply ConcreteCategory.hom_ext
    intro y
    rw [ConcreteCategory.comp_apply, TypeCat.ofHom_apply]
    apply huniq
    exact (hex (c'.ι.app ⟨j⟩ y)).choose_spec.choose_spec
  · intro s m hm
    apply ConcreteCategory.hom_ext
    intro p
    rw [TypeCat.ofHom_apply]
    have hp := (hex p).choose_spec.choose_spec
    have h2 := ConcreteCategory.congr_hom (hm ⟨(hex p).choose⟩) (hex p).choose_spec.choose
    rw [ConcreteCategory.comp_apply] at h2
    exact (congrArg (ConcreteCategory.hom m) hp).symm.trans h2

/-- **Infinitary universality of coproducts of presheaves of types.** For an arbitrary index
type `I` and a family `Hi : I → (Cᵒᵖ ⥤ Type max u v)` of presheaves, the coproduct cocone
`Cofan.mk (∐ Hi) (Sigma.ι Hi)` is a universal colimit. -/
@[sga "4 I 3.3" "special case",
  sga "4 II 4.3" "Clause 1, special case",
  sga "4 II 4.5.1" "partial",
  sga "4 II 4.8" "special case",
  sga "4 IV 1.1.2" "b), special case"]
lemma presheaf_coproduct_isUniversalColimit {I : Type max u v}
    (Hi : I → (Cᵒᵖ ⥤ Type max u v)) [HasCoproduct Hi] :
    IsUniversalColimit (Cofan.mk (∐ Hi) (Sigma.ι Hi)) := by
  intro F' c' α f h hα hpb
  refine ⟨evaluationJointlyReflectsColimits c' (fun K => ?_)⟩
  set evK := (evaluation Cᵒᵖ (Type max u v)).obj K with hevK
  have hcol : IsColimit (evK.mapCocone (Cofan.mk (∐ Hi) (Sigma.ι Hi))) :=
    isColimitOfPreserves evK (coproductIsCoproduct Hi)
  have huniv := presheaf_coproduct_isUniversalColimit.typeColimitUniversal _ _ hcol
  refine huniv (evK.mapCocone c') (Functor.whiskerRight α evK) (evK.map f) ?_ ?_ ?_ |>.some
  · ext j x
    exact ConcreteCategory.congr_hom (congrArg evK.map (congr_app h j)) x
  · exact hα.whiskerRight evK
  · exact fun j => (hpb j).map evK

/-- **Infinitary universality of coproducts in `Sh(C)`.** The coproduct cocone
`Cofan.mk (∐ Gi) (Sigma.ι Gi)` of an arbitrary family of sheaves of sets is a universal
colimit, i.e. it stays a colimit after base change. -/
@[sga "4 I 3.3" "special case",
  sga "4 II 4.3" "clause 1 for coproducts",
  sga "4 II 4.5.1" "partial",
  sga "4 II 4.8" "b)",
  sga "4 IV 1.1.2"]
lemma Sheaf.coproduct_isUniversalColimit {I : Type max u v}
    (Gi : I → Sheaf J (Type max u v)) [HasCoproduct Gi] :
    IsUniversalColimit (Cofan.mk (∐ Gi) (Sigma.ι Gi)) := by
  classical
  set Gl := presheafToSheaf J (Type max u v) with hGl
  set Gr := sheafToPresheaf J (Type max u v) with hGr
  have adj : Gl ⊣ Gr := sheafificationAdjunction J (Type max u v)
  set Fdia : Discrete I ⥤ Sheaf J (Type max u v) := Discrete.functor Gi with hFdia
  set Hi : I → (Cᵒᵖ ⥤ Type max u v) := fun i => Gr.obj (Gi i) with hHi
  have : HasCoproduct Hi := inferInstance
  have hpres : IsUniversalColimit (Cofan.mk (∐ Hi) (Sigma.ι Hi)) :=
    presheaf_coproduct_isUniversalColimit Hi
  have diso : (Fdia ⋙ Gr) ≅ Discrete.functor Hi := Discrete.natIso (fun _ => Iso.refl _)
  have hc : IsUniversalColimit ((Cocone.precompose diso.hom).obj (Cofan.mk (∐ Hi) (Sigma.ι Hi))) :=
    hpres.precompose_isIso diso.hom
  have huniv : IsUniversalColimit
      (Gl.mapCocone ((Cocone.precompose diso.hom).obj (Cofan.mk (∐ Hi) (Sigma.ι Hi)))) :=
    hc.map_reflective adj
  have : IsIso adj.counit := inferInstance
  have ccIso : (Gr ⋙ Gl) ≅ 𝟭 (Sheaf J (Type max u v)) := asIso adj.counit
  have eFin : ((Fdia ⋙ Gr) ⋙ Gl) ≅ Fdia :=
    (Functor.associator Fdia Gr Gl) ≪≫ Functor.isoWhiskerLeft Fdia ccIso ≪≫ Fdia.rightUnitor
  have huniv2 : IsUniversalColimit ((Cocone.precompose eFin.inv).obj
      (Gl.mapCocone ((Cocone.precompose diso.hom).obj (Cofan.mk (∐ Hi) (Sigma.ι Hi))))) :=
    huniv.precompose_isIso eFin.inv
  exact huniv2.of_iso (huniv2.isColimit.uniqueUpToIso (coproductIsCoproduct Gi))

/-- **Pullback-stability of epimorphisms in the sheaf topos** (regularity of the topos).

The base change `pullback.snd f g` of an epimorphism `f` along any morphism `g` is again an
epimorphism. -/
@[sga "3 IV 1.11" "partial",
  sga "3 IV 4.5.7",
  sga "3 IV 4.5.8" "Epimorphism clause",
  sga "4 IV 8.5.1" "partial"]
lemma Sheaf.epi_pullback_snd {X Y Z : Sheaf J (Type max u v)} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g] (hf : Epi f) : Epi (pullback.snd f g) := by
  have pres_lsurj_bc : ∀ {P X Y Z : Cᵒᵖ ⥤ Type max u v} (fst : P ⟶ X) (snd : P ⟶ Y)
      (f : X ⟶ Z) (g : Y ⟶ Z), IsPullback fst snd f g → Presheaf.IsLocallySurjective J f →
      Presheaf.IsLocallySurjective J snd := by
    intro P X Y Z fst snd f g sq hfls
    constructor
    intro U s
    have hfm := Presheaf.imageSieve_mem J f (g.app (Opposite.op U) s)
    apply J.superset_covering _ hfm
    intro V i hi
    rw [Presheaf.imageSieve_apply] at hi ⊢
    obtain ⟨t, ht⟩ := hi
    have sqV : IsPullback (fst.app (Opposite.op V)) (snd.app (Opposite.op V))
        (f.app (Opposite.op V)) (g.app (Opposite.op V)) :=
      sq.map ((evaluation Cᵒᵖ (Type max u v)).obj (Opposite.op V))
    rw [Types.isPullback_iff] at sqV
    obtain ⟨p, -, hp⟩ := sqV.2.2 t (Y.map i.op s) (by rw [NatTrans.naturality_apply g i.op s, ht])
    exact ⟨p, hp⟩
  rw [← Sheaf.isLocallySurjective_iff_epi,
    ← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff] at hf ⊢
  exact pres_lsurj_bc _ _ _ _
    ((IsPullback.of_hasPullback f g).map (sheafToPresheaf J (Type max u v))) hf

/-- **Reassembly.** A morphism `r : Z ⟶ F ⨿ G` into a binary coproduct is an epimorphism if its
pullbacks `pullback.snd r coprod.inl` and `pullback.snd r coprod.inr` along the two coprojections
are both epimorphisms. -/
lemma Sheaf.epi_of_pullback_snd_epi {F G Z : Sheaf J (Type max u v)} [HasBinaryCoproduct F G]
    (r : Z ⟶ F ⨿ G)
    [HasPullback r (coprod.inl : F ⟶ F ⨿ G)] [HasPullback r (coprod.inr : G ⟶ F ⨿ G)]
    (hF : Epi (pullback.snd r (coprod.inl : F ⟶ F ⨿ G)))
    (hG : Epi (pullback.snd r (coprod.inr : G ⟶ F ⨿ G))) : Epi r := by
  have key : ∀ {X : Sheaf J (Type max u v)} (i : X ⟶ F ⨿ G) [HasPullback r i],
      Epi (pullback.snd r i) → ∀ {W : Sheaf J (Type max u v)} (a b : F ⨿ G ⟶ W),
        r ≫ a = r ≫ b → i ≫ a = i ≫ b := by
    intro X i _ hi W a b hab
    rw [← cancel_epi (pullback.snd r i), ← Category.assoc, ← Category.assoc,
      ← pullback.condition, Category.assoc, Category.assoc, hab]
  constructor
  intro W a b hab
  exact coprod.hom_ext (key _ hF a b hab) (key _ hG a b hab)

/-- The colimit `desc` of the standard coproduct cocone agrees with `Sigma.desc`. -/
private lemma Sheaf.coproductIsColimitDesc_eq {β : Type max u v}
    (X : β → Sheaf J (Type max u v)) [HasCoproduct X] {A : Sheaf J (Type max u v)}
    (g : (i : β) → X i ⟶ A) :
    Cofan.IsColimit.desc (coproductIsCoproduct X) g = Sigma.desc g := by
  refine ((coproductIsCoproduct X).uniq (Cofan.mk A g) (Sigma.desc g) ?_).symm
  rintro ⟨j⟩
  simp

/-- In the sheaf topos, the second projection of the chosen pullback of `f` and `g` is epi
whenever the second projection `b` of some pullback square of `f` and `g` is epi. -/
private lemma Sheaf.epi_pullback_snd_of_isPullback {P X Y Z : Sheaf J (Type max u v)}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g)
    [HasPullback f g] (hb : Epi b) : Epi (pullback.snd f g) :=
  epi_of_epi_fac h.isoPullback_hom_snd

/-- Precomposing `Sigma.desc g` with the map induced by reindexing along `e` gives the `desc`
of the reindexed family. -/
private lemma map'_id_comp_desc {D : Type*} [Category D] {α β : Type*} (P : β → D) {A : D}
    (g : (b : β) → P b ⟶ A) (e : α → β) [HasCoproduct P] [HasCoproduct (fun a => P (e a))] :
    Sigma.map' e (fun a => 𝟙 (P (e a))) ≫ Sigma.desc g = Sigma.desc (fun a => g (e a)) := by
  ext a
  simp

/-- Index enlargement: if the `desc` of `g` over `S₀ ⊆ S` is epi, so is the `desc` over `S`. -/
private lemma Sheaf.epi_desc_enlarge {I : Type max u v}
    (P : I → Sheaf J (Type max u v)) {A : Sheaf J (Type max u v)}
    (g : (i : I) → P i ⟶ A) (S₀ S : Finset I) (hsub : S₀ ⊆ S)
    [HasCoproduct (fun j : S₀ => P j.1)] [HasCoproduct (fun j : S => P j.1)]
    (hepi : Epi (Sigma.desc (fun j : S₀ => g j.1))) :
    Epi (Sigma.desc (fun j : S => g j.1)) := by
  refine epi_of_epi_fac (h := Sigma.desc fun j : S₀ => g j.1)
    (f := Sigma.desc fun j : S₀ => Sigma.ι (fun j : S => P j.1) ⟨j.1, hsub j.2⟩) ?_
  ext j
  simp

/-- If `F` and `G` are quasi-compact, then for every family `Gi` with a coproduct and every
epimorphism `φ : ∐ Gi ⟶ F ⨿ G` there is a finite `S` such that the restriction
`∐_{j ∈ S} Gi j ⟶ F ⨿ G` of `φ` is an epimorphism. -/
@[sga "4 VI 1.4" "partial"]
lemma Sheaf.QuasiCompact.binaryCoproduct_aux {F G : Sheaf J (Type max u v)}
    [HasBinaryCoproduct F G]
    (hF : Sheaf.QuasiCompact F) (hG : Sheaf.QuasiCompact G)
    {I : Type max u v} (Gi : I → Sheaf J (Type max u v)) [HasCoproduct Gi]
    (φ : ∐ Gi ⟶ F ⨿ G) (hφ : Epi φ) :
    ∃ (S : Finset I), ∃ _ : HasCoproduct (fun j : S => Gi j.1),
      Epi (Sigma.desc (fun j : S => Sigma.ι Gi j.1 ≫ φ)) := by
  classical
  have hcolim : HasColimitsOfSize.{max u v, max u v} (Sheaf J (Type max u v)) :=
    Sheaf.instHasColimitsOfSize
  have side : ∀ (B : Sheaf J (Type max u v)) (vv : B ⟶ F ⨿ G), Sheaf.QuasiCompact B →
      ∃ Sv : Finset I, ∀ (S : Finset I), Sv ⊆ S →
        ∀ [HasCoproduct (fun j : S => Gi j.1)]
          [HasPullback (Sigma.desc (fun j : S => Sigma.ι Gi j.1 ≫ φ)) vv],
        Epi (pullback.snd (Sigma.desc (fun j : S => Sigma.ι Gi j.1 ≫ φ)) vv) := by
    intro B vv hB
    set Pb : I → Sheaf J (Type max u v) := fun i => pullback vv (Sigma.ι Gi i ≫ φ) with hPb
    set q1 : (i : I) → Pb i ⟶ B := fun i => pullback.fst vv (Sigma.ι Gi i ≫ φ) with hq1
    set q2 : (i : I) → Pb i ⟶ Gi i := fun i => pullback.snd vv (Sigma.ι Gi i ≫ φ) with hq2
    have hsq : ∀ i, IsPullback (q1 i) (q2 i) vv (Sigma.ι Gi i ≫ φ) :=
      fun i => IsPullback.of_hasPullback _ _
    have hd : IsColimit (Cofan.mk (∐ Pb) (Sigma.ι Pb)) := coproductIsCoproduct Pb
    have key := (Sheaf.coproduct_isUniversalColimit Gi).isPullback_of_isColimit_left
      (fun i => Sigma.ι Gi i ≫ φ) φ vv q1 q2 hsq hd
    set ΨB : (∐ Pb) ⟶ B := Cofan.IsColimit.desc hd q1
    have hΨepi : Epi ΨB := by
      have he : key.flip.isoPullback.hom ≫ pullback.snd φ vv = ΨB := key.flip.isoPullback_hom_snd
      have : Epi (pullback.snd φ vv) := Sheaf.epi_pullback_snd φ vv hφ
      rw [← he]; exact epi_comp _ _
    obtain ⟨Sv, hSvcop, hSvepi⟩ := hB Pb ΨB hΨepi
    refine ⟨Sv, ?_⟩
    intro S hsub instCop instPb
    have : HasCoproduct (fun j : S => Pb j.1) := inferInstance
    have hEnl : Epi (Sigma.desc (fun j : S => Sigma.ι Pb j.1 ≫ ΨB)) :=
      Sheaf.epi_desc_enlarge Pb (fun i => Sigma.ι Pb i ≫ ΨB) Sv S hsub hSvepi
    set Gi' : S → Sheaf J (Type max u v) := fun j => Gi j.1 with hGi'
    set r : (∐ Gi') ⟶ F ⨿ G := Sigma.desc (fun j : S => Sigma.ι Gi j.1 ≫ φ) with hr
    have hcompat : ∀ j : S, (Cofan.mk (∐ Gi') (Sigma.ι Gi')).inj j ≫ r = Sigma.ι Gi j.1 ≫ φ := by
      intro j
      simp [hr]
    have hd' : IsColimit (Cofan.mk (∐ fun j : S => Pb j.1) (Sigma.ι (fun j : S => Pb j.1))) :=
      coproductIsCoproduct (fun j : S => Pb j.1)
    have hsq' : ∀ j : S, IsPullback (q1 j.1) (q2 j.1) vv (Sigma.ι Gi j.1 ≫ φ) := fun j => hsq j.1
    have keyS := (Sheaf.coproduct_isUniversalColimit Gi').isPullback_of_isColimit_left
      (fun j : S => Sigma.ι Gi j.1 ≫ φ) r vv (fun j => q1 j.1) (fun j => q2 j.1) hsq'
      (coproductIsCoproduct (fun j : S => Pb j.1)) hcompat
    set rF : (∐ fun j : S => Pb j.1) ⟶ B :=
      Cofan.IsColimit.desc (coproductIsCoproduct (fun j : S => Pb j.1)) (fun j => q1 j.1) with hrF
    have hrFepi : Epi rF := by
      have e1 : rF = Sigma.desc (fun j : S => q1 j.1) := by
        rw [hrF]; exact Sheaf.coproductIsColimitDesc_eq (fun j : S => Pb j.1) (fun j => q1 j.1)
      have e2 : (fun j : S => q1 j.1) = (fun j : S => Sigma.ι Pb j.1 ≫ ΨB) := by
        funext j
        exact (Cofan.IsColimit.fac hd q1 j.1).symm
      rw [e1, e2]; exact hEnl
    have := Sheaf.epi_pullback_snd_of_isPullback keyS.flip hrFepi
    simpa [hr] using this
  obtain ⟨SF, hSF⟩ := side F coprod.inl hF
  obtain ⟨SG, hSG⟩ := side G coprod.inr hG
  have hcs : HasColimitsOfShape (Discrete (SF ∪ SG : Finset I)) (Sheaf J (Type max u v)) :=
    inferInstance
  have hScop : HasCoproduct (fun j : (SF ∪ SG : Finset I) => Gi j.1) :=
    hcs.has_colimit (Discrete.functor (fun j : (SF ∪ SG : Finset I) => Gi j.1))
  refine ⟨SF ∪ SG, hScop, ?_⟩
  set r : (∐ fun j : (SF ∪ SG : Finset I) => Gi j.1) ⟶ F ⨿ G :=
    Sigma.desc (fun j : (SF ∪ SG : Finset I) => Sigma.ι Gi j.1 ≫ φ) with hr
  have hpl : HasPullback r (coprod.inl : F ⟶ F ⨿ G) := inferInstance
  have hpr : HasPullback r (coprod.inr : G ⟶ F ⨿ G) := inferInstance
  have hEF : Epi (pullback.snd r (coprod.inl : F ⟶ F ⨿ G)) :=
    hSF (SF ∪ SG) (Finset.subset_union_left)
  have hEG : Epi (pullback.snd r (coprod.inr : G ⟶ F ⨿ G)) :=
    hSG (SF ∪ SG) (Finset.subset_union_right)
  exact Sheaf.epi_of_pullback_snd_epi r hEF hEG

/-- **The binary case of Stacks 0GMQ.** The coproduct `F ⨿ G` of two quasi-compact sheaves is
quasi-compact. -/
@[sga "4 VI 1.4" "partial"]
theorem Sheaf.QuasiCompact.binaryCoproduct {F G : Sheaf J (Type max u v)}
    [HasBinaryCoproduct F G]
    (hF : Sheaf.QuasiCompact F) (hG : Sheaf.QuasiCompact G) :
    Sheaf.QuasiCompact (F ⨿ G) :=
  fun Gi _ φ hφ => hF.binaryCoproduct_aux hG Gi φ hφ

/-- **Stacks Tag 0GMQ, Lemma 7.17.6.**

Let `C` be a site and let `n ≥ 1`. If `F : Fin n → Sh(C)` is a finite family of
quasi-compact sheaves (quasi-compact objects of the topos `Sh(C)` in the sense of
`Sheaf.QuasiCompact`), then their coproduct `∐ F` in `Sh(C)` is quasi-compact.

The family is indexed by `Fin n` with `n ≥ 1`, the `0`-indexed form of the family
`F_1, …, F_n` of the informal statement. -/
@[stacks 0GMQ, sga "4 VI 1.3" "special case", sga "4 VI 1.4" "partial"]
theorem Sheaf.quasiCompact_coproduct_fin
    {n : ℕ} (hn : 1 ≤ n) (F : Fin n → Sheaf J (Type max u v))
    [HasCoproduct F]
    (hF : ∀ i, Sheaf.QuasiCompact (F i)) :
    Sheaf.QuasiCompact (∐ F) := by
  induction n with
  | zero => omega
  | succ m ih =>
    set T : Fin m → Sheaf J (Type max u v) := fun i => F i.succ with hT
    -- The instances are built from `HasFiniteCoproducts`: plain `inferInstance` exceeds the
    -- typeclass heartbeat limit here.
    have hfc : HasFiniteCoproducts (Sheaf J (Type max u v)) := inferInstance
    have hcsF : HasColimitsOfShape (Discrete (Fin m)) (Sheaf J (Type max u v)) := hfc.out m
    have hTcop : HasCoproduct T := hcsF.has_colimit (Discrete.functor T)
    have hcsW : HasColimitsOfShape (Discrete WalkingPair) (Sheaf J (Type max u v)) :=
      hasColimitsOfShape_discrete _ WalkingPair
    have hbc : HasBinaryCoproduct (F 0) (∐ T) := hcsW.has_colimit (pair (F 0) (∐ T))
    have hF0 : Sheaf.QuasiCompact (F 0) := hF 0
    have hiso : (∐ F) ≅ (F 0 ⨿ ∐ T) :=
      (coproductIsCoproduct F).coconePointUniqueUpToIso
        (extendCofanIsColimit F (coproductIsCoproduct T) (coprodIsCoprod (F 0) (∐ T)))
    have hbin : Sheaf.QuasiCompact (F 0 ⨿ ∐ T) := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        have hTinit : Limits.IsInitial (∐ T) :=
          { desc := fun s => (coproductIsCoproduct T).desc
              (Cofan.mk s.pt (fun j => j.elim0))
            fac := fun s j => j.as.elim
            uniq := fun s f _ => by
              apply (coproductIsCoproduct T).hom_ext
              intro j
              exact j.as.elim0 }
        have hcolim : Limits.IsColimit
            (BinaryCofan.mk (𝟙 (F 0)) (hTinit.to (F 0))) :=
          BinaryCofan.isColimitMk
            (fun s => s.inl)
            (fun s => by simp)
            (fun s => hTinit.hom_ext _ _)
            (fun s m hm₁ _ => by simpa using hm₁)
        intro I Gi _ φ hφ
        exact Sheaf.QuasiCompact.of_iso
          ((coprodIsCoprod (F 0) (∐ T)).coconePointUniqueUpToIso hcolim).symm hF0 Gi φ hφ
      · exact hF0.binaryCoproduct (ih hm T (fun i => hF i.succ))
    -- With the `set`-bound `T` in context `Sheaf.QuasiCompact` does not refold, so the goal
    -- is introduced first.
    intro I Gi _ φ hφ
    exact Sheaf.QuasiCompact.of_iso hiso.symm hbin Gi φ hφ

/-! ### The two spellings of Stacks 0D07 agree -/

/-- The `Epi`-and-`Finset` spelling of **Stacks 0D07** follows from the
`IsLocallySurjective`-and-finite-`Set` one. -/
theorem Sheaf.quasiCompact_of_isQuasiCompact {F : Sheaf J (Type max u v)}
    (hF : Sheaf.IsQuasiCompact F) : Sheaf.QuasiCompact F := by
  intro I Fi _ φ hφ
  have hls : Sheaf.IsLocallySurjective (Sigma.desc fun i => Sigma.ι Fi i ≫ φ) := by
    rwa [show (Sigma.desc fun i => Sigma.ι Fi i ≫ φ) = φ by ext; simp,
      Sheaf.isLocallySurjective_iff_epi]
  obtain ⟨T, hTfin, hT⟩ := hF I Fi (fun i => Sigma.ι Fi i ≫ φ) hls
  refine ⟨hTfin.toFinset, inferInstance, ?_⟩
  have : Epi (Sigma.desc fun k : (T : Type max u v) => Sigma.ι Fi k.1 ≫ φ) :=
    (Sheaf.isLocallySurjective_iff_epi _).1 hT
  exact epi_of_epi_fac (map'_id_comp_desc (fun j : (hTfin.toFinset : Finset I) => Fi j.1)
    (fun j => Sigma.ι Fi j.1 ≫ φ)
    (fun k : (T : Type max u v) => ⟨k.1, hTfin.mem_toFinset.2 k.2⟩))

/-- The `IsLocallySurjective`-and-finite-`Set` spelling of **Stacks 0D07** follows from the
`Epi`-and-`Finset` one. -/
theorem Sheaf.isQuasiCompact_of_quasiCompact {F : Sheaf J (Type max u v)}
    (hF : Sheaf.QuasiCompact F) : Sheaf.IsQuasiCompact F := by
  intro I G f hf
  have hepi : Epi (Sigma.desc f) := (Sheaf.isLocallySurjective_iff_epi _).1 hf
  obtain ⟨S, hSc, hS⟩ := hF G (Sigma.desc f) hepi
  refine ⟨(S : Set I), S.finite_toSet, ?_⟩
  simp only [Sigma.ι_comp_desc] at hS
  rw [Sheaf.isLocallySurjective_iff_epi]
  exact epi_of_epi_fac (map'_id_comp_desc (fun j : ((S : Set I) : Type max u v) => G j.1)
    (fun j => f j.1) (fun j : (S : Finset I) => ⟨j.1, Finset.mem_coe.2 j.2⟩))

/-- **The two spellings of Stacks 0D07 define the same predicate.** One phrases surjectivity of
`∐_{i ∈ I} F_i ⟶ F` as `CategoryTheory.Epi` and the finite subset as a `Finset`
(`Sheaf.QuasiCompact`), the other as
`CategoryTheory.Sheaf.IsLocallySurjective` with a finite `Set`
(`CategoryTheory.Sheaf.IsQuasiCompact`).

With this, Stacks 0GMQ — `Sheaf.quasiCompact_coproduct_fin`, stated in the first
spelling — applies to the hypothesis of Stacks 0GMR part (4), stated in the second. -/
theorem Sheaf.quasiCompact_iff_isQuasiCompact {F : Sheaf J (Type max u v)} :
    Sheaf.QuasiCompact F ↔ Sheaf.IsQuasiCompact F :=
  ⟨Sheaf.isQuasiCompact_of_quasiCompact, Sheaf.quasiCompact_of_isQuasiCompact⟩
