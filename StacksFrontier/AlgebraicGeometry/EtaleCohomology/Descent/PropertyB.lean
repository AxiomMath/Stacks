module

public import Mathlib.AlgebraicGeometry.Sites.Pretopology
public import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.Basic

/-!
# Direct image of sheaves of sets along a morphism with property (B)

Let `f : X ⟶ Y` be a morphism of schemes with property (B): every étale covering of an étale
base change `X ×ₗᵧ V` of `f` is refined, after a further étale covering of `V`, by disjoint
union decompositions subordinate to it. Direct image along the induced morphism of small étale
sites then carries surjections of sheaves of sets to surjections.

The reason is that a surjection of sheaves on the small étale site of `X` is locally surjective,
so a section of the target over `X ×ₗᵧ V` lifts over the members of some étale covering of
`X ×ₗᵧ V`. Property (B) replaces that covering by an étale covering `{V_j ⟶ V}` over which
`X ×ₗᵧ V_j` is a *disjoint union* of pieces subordinate to it. On a disjoint union the local
lifts are automatically compatible, because an object mapping into two distinct summands has
empty underlying scheme and hence only one section; so the sheaf condition glues them to a
single lift over `X ×ₗᵧ V_j`, that is, to a lift of the section of the direct image over `V_j`.

Property (B) itself, and the reduction of it to a pointwise condition on the base, are in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.Basic`.

## Main results

* `Stacks.EtaleCohomology.smallEtalePushforward_preservesEpimorphisms_of_hasPropertyB` — for a
  morphism with property (B), direct image of sheaves of sets on small étale sites preserves
  surjections.

## Implementation notes

Surjections of sheaves of sets are the epimorphisms, and they are detected by local
surjectivity. The statement is universe polymorphic in the coefficients: when the coefficient
universe is too small to contain the site, a sheaf of sets on the small étale site has at most
one section over every object, and the assertion is vacuous.

## References

* [Stacks Project, Tag 04DO](https://stacks.math.columbia.edu/tag/04DO)
* [Stacks Project, Tag 04D7](https://stacks.math.columbia.edu/tag/04D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

/-- A sheaf of sets on the small étale site has at most one section over an object with empty
underlying scheme, because the empty family covers such an object. -/
public lemma subsingleton_sections_of_isEmpty {X : Scheme.{u}}
    (F : Sheaf (smallEtaleTopology X) (Type w)) (Z : X.Etale) (hZ : IsEmpty Z.left) :
    Subsingleton (F.obj.obj (op Z)) := by
  classical
  let Z₀ : PEmpty.{1} → X.Etale := fun i ↦ PEmpty.elim i
  let g : ∀ i : PEmpty.{1}, Z₀ i ⟶ Z := fun i ↦ PEmpty.elim i
  have hbot : Sieve.ofArrows Z₀ g = ⊥ := by
    simp [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty]
  have hpoints : (⋃ i : PEmpty.{1}, Set.range (g i).left) = Set.univ := by
    ext x
    simp [hZ.false x]
  have hcov := (Scheme.ofArrows_mem_smallEtaleTopology_iff g).2 hpoints
  have hbotcov : (⊥ : Sieve Z) ∈ smallEtaleTopology X Z := by
    simpa [hbot] using hcov
  have hterm : IsTerminal (F.obj.obj (op Z)) := Sheaf.isTerminalOfBotCover F Z hbotcov
  let : Unique (F.obj.obj (op Z)) := Types.isTerminalEquivUnique (F.obj.obj (op Z)) hterm
  exact inferInstance

/-- The inclusions of a family of étale objects, composed with an isomorphism from the coproduct
of their underlying schemes, cover the target. -/
private lemma ofArrows_mem_smallEtaleTopology_of_iso_sigma {X : Scheme.{u}} {I : Type u}
    {Z : X.Etale} (D : I → X.Etale) (k : ∀ i, D i ⟶ Z)
    (φ : ∐ (fun i ↦ (D i).left) ≅ Z.left)
    (hk : ∀ i, (k i).left = Sigma.ι (fun i ↦ (D i).left) i ≫ φ.hom) :
    Sieve.ofArrows D k ∈ smallEtaleTopology X Z := by
  refine (Scheme.ofArrows_mem_smallEtaleTopology_iff k).2 (Set.eq_univ_of_forall fun z ↦ ?_)
  let e := AlgebraicGeometry.sigmaMk (fun i ↦ (D i).left)
  rcases hpair : (e.toEquiv.symm (φ.inv z) : Σ i, (D i).left) with ⟨i, a⟩
  have hz := e.toEquiv.apply_symm_apply (φ.inv z)
  rw [hpair] at hz
  change AlgebraicGeometry.sigmaMk (fun i ↦ (D i).left) (.mk i a) = _ at hz
  rw [AlgebraicGeometry.sigmaMk_mk] at hz
  refine Set.mem_iUnion.2 ⟨i, a, ?_⟩
  rw [hk, Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply]
  simp

/-- Sections of a sheaf over the pieces `D i` of a disjoint union decomposition glue to a section
over the whole, since sections over the empty overlaps of distinct pieces are unique. -/
private lemma exists_section_of_iso_sigma {X : Scheme.{u}}
    (F : Sheaf (smallEtaleTopology X) (Type w)) {I : Type u} {Z : X.Etale} (D : I → X.Etale)
    (k : ∀ i, D i ⟶ Z) (φ : ∐ (fun i ↦ (D i).left) ≅ Z.left)
    (hk : ∀ i, (k i).left = Sigma.ι (fun i ↦ (D i).left) i ≫ φ.hom)
    (s : ∀ i, F.obj.obj (op (D i))) :
    ∃ t : F.obj.obj (op Z), ∀ i, F.obj.map (k i).op t = s i := by
  have hsh : Presieve.IsSheafFor F.obj (Presieve.ofArrows D k) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact (isSheaf_iff_isSheaf_of_type _ F.obj).1 F.property _
      (ofArrows_mem_smallEtaleTopology_of_iso_sigma D k φ hk)
  apply ((Presieve.isSheafFor_arrows_iff F.obj k).1 hsh s ?_).exists
  intro i j T a b hab
  have h : a.left ≫ (k i).left = b.left ≫ (k j).left := congrArg (fun t ↦ t.left) hab
  rw [hk, hk] at h
  have h' : a.left ≫ Sigma.ι (fun i ↦ (D i).left) i = b.left ≫ Sigma.ι (fun i ↦ (D i).left) j :=
    (cancel_mono φ.hom).1 (by simpa only [Category.assoc] using h)
  by_cases hij : i = j
  · subst j
    obtain rfl : a = b := MorphismProperty.Over.Hom.ext ((cancel_mono _).1 h')
    rfl
  · have : IsEmpty T.left := AlgebraicGeometry.isEmpty_of_commSq_sigmaι_of_ne ⟨h'⟩ hij
    have := subsingleton_sections_of_isEmpty F T inferInstance
    exact Subsingleton.elim _ _

/-- If some sheaf of sets on the small étale site of `X` has two distinct sections over an
object `U`, then the coefficient universe is at least as large as the universe of `X`: an
arbitrary index type `I` is encoded by the characteristic functions of its elements, glued over
the covering of the `I`-fold disjoint union of `U` by its summands. -/
private lemma univLE_of_ne_sections {X : Scheme.{u}} (F : Sheaf (smallEtaleTopology X) (Type v))
    (U : X.Etale) (x y : F.obj.obj (op U)) (hxy : x ≠ y) : UnivLE.{u, v} := by
  classical
  refine ⟨fun I ↦ ?_⟩
  let W : I → Scheme.{u} := fun _ ↦ U.left
  let p : (∐ W) ⟶ X := Sigma.desc (fun _ : I ↦ U.hom)
  let : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  have hp : Etale p := IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun _ ↦ U.prop)
  let Z : X.Etale := MorphismProperty.Over.mk _ p hp
  let k : ∀ i : I, U ⟶ Z := fun i ↦
    MorphismProperty.Over.homMk (Sigma.ι W i) (by change Sigma.ι W i ≫ p = U.hom; simp [p])
  have hglue (s : I → F.obj.obj (op U)) :
      ∃ t : F.obj.obj (op Z), ∀ i, F.obj.map (k i).op t = s i :=
    exists_section_of_iso_sigma F (fun _ : I ↦ U) k (Iso.refl _)
      (fun i ↦ (Category.comp_id _).symm) s
  let indicator (i j : I) : F.obj.obj (op U) := if j = i then x else y
  apply small_of_injective_of_exists (fun t i ↦ F.obj.map (k i).op t) (g := indicator) ?_ ?_
  · intro i j hij
    by_contra hne
    have heq := congrFun hij i
    exact hxy (by simpa [indicator, hne] using heq)
  · intro i
    obtain ⟨t, ht⟩ := hglue (indicator i)
    exact ⟨t, funext ht⟩

/-- The heart of the matter: under property (B), a section of a sheaf of sets over a base change
`X ×_Y V` which is locally in the image of a locally surjective map of sheaves is, after passing
to a suitable étale covering of `V`, globally in the image over the corresponding base
changes. -/
private lemma sectionLifting_of_hasPropertyB {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : HasPropertyB f) :
    ∀ {F G : Sheaf (smallEtaleTopology X) (Type v)} (η : F ⟶ G)
      [Sheaf.IsLocallySurjective η] (V : Y.Etale)
      (s : G.obj.obj (op ((smallEtaleBaseChange f).obj V))),
      ∃ (I : Type (u + 1)) (W : I → Y.Etale) (g : ∀ i, W i ⟶ V),
        Sieve.ofArrows W g ∈ smallEtaleTopology Y V ∧
        ∀ i, ∃ t : F.obj.obj (op ((smallEtaleBaseChange f).obj (W i))),
          η.hom.app (op ((smallEtaleBaseChange f).obj (W i))) t =
            G.obj.map ((smallEtaleBaseChange f).map (g i)).op s := by
  intro F G η hη V s
  let P : X.Etale := (smallEtaleBaseChange f).obj V
  let R : Sieve P := Presheaf.imageSieve η.hom s
  have hR : R ∈ smallEtaleTopology X P := hη.imageSieve_mem s
  let : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) := by
    apply MorphismProperty.RespectsIso.mk <;>
    · intro A B C i g hg
      have : Etale g := hg
      infer_instance
  obtain ⟨𝒰, hOver, hEt, hle⟩ :=
    (Scheme.mem_smallGrothendieckTopology (P := @Etale.{u}) (S := X) P R).1 hR
  have : Etale V.hom := V.prop
  let eSymm : P.left ≅ Limits.pullback f V.hom := pullbackSymmetry V.hom f
  let : Etale eSymm.hom := inferInstance
  let 𝒰' : (Limits.pullback f V.hom).Cover Scheme.etalePrecoverage :=
    Scheme.Cover.mkOfCovers (P := @Etale.{u}) 𝒰.I₀ 𝒰.X (fun i ↦ 𝒰.f i ≫ eSymm.hom)
      (fun x ↦ by
        have hcover : ∀ z : P.left, ∃ i, z ∈ Set.range (𝒰.f i) :=
          (Scheme.ofArrows_mem_precoverage_iff (P := @Etale.{u})
            (X := 𝒰.X) (f := 𝒰.f)).1 𝒰.mem₀ |>.1
        obtain ⟨i, y, hy⟩ := hcover (eSymm.inv x)
        refine ⟨i, y, ?_⟩
        rw [Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply]
        simp)
      (fun i ↦ by
        let : Etale (𝒰.f i) := 𝒰.map_prop i
        infer_instance)
  obtain ⟨𝒱, hpiece⟩ := hf V.hom 𝒰'
  choose q hqfst hqsnd W e a hcomp using hpiece
  let : Scheme.IsJointlySurjectivePreserving (@Etale : MorphismProperty Scheme.{u}) :=
    Scheme.isJointlySurjectivePreserving @Etale
  let : Scheme.etalePrecoverage.IsStableUnderBaseChange := by
    let Q : MorphismProperty Scheme.{u} := @Etale
    show (Scheme.precoverage Q).IsStableUnderBaseChange
    let : Scheme.IsJointlySurjectivePreserving Q := Scheme.isJointlySurjectivePreserving Q
    let : Q.IsStableUnderBaseChange := by infer_instance
    exact inferInstance
  let : 𝒰.Over X := hOver
  let : Category.{u, u + 1}
      (MorphismProperty.Over (@Etale : MorphismProperty Scheme.{u}) ⊤ X) := X.instCategoryEtale
  let : OverClass P.left X := ⟨P.hom⟩
  let (i : 𝒰.I₀) : OverClass (𝒰.X i) X := hOver.over i
  let (i : 𝒰.I₀) : Hom.IsOver (𝒰.f i) X := hOver.isOver_map i
  let (i : 𝒰.I₀) : Etale (𝒰.X i ↘ X) := hEt i
  let liftArrow (i : 𝒰.I₀) : Etale.mk (𝒰.X i ↘ X) ⟶ P :=
    @MorphismProperty.Over.homMk Scheme.{u} (inferInstance : Category.{u, u + 1} Scheme.{u})
      (@Etale : MorphismProperty Scheme.{u}) (⊤ : MorphismProperty Scheme.{u}) X
      (inferInstance : (⊤ : MorphismProperty Scheme.{u}).IsMultiplicative)
      (Etale.mk (𝒰.X i ↘ X)) P (𝒰.f i) (hOver.isOver_map i).1 (by trivial)
  have hlift (i : 𝒰.I₀) :
      ∃ t : F.obj.obj (op (Etale.mk (𝒰.X i ↘ X))),
        η.hom.app (op (Etale.mk (𝒰.X i ↘ X))) t = G.obj.map (liftArrow i).op s :=
    hle ((𝒰.X i).asOverProp X (hEt i)) ((𝒰.f i).asOverProp X) ⟨i⟩
  let g := V.hom
  let I := ULift.{u + 1, u} 𝒱.I₀
  let (j : 𝒱.I₀) : OverClass (𝒱.X j) Y := ⟨𝒱.f j ≫ g⟩
  have hVjEt : ∀ j : 𝒱.I₀, Etale (𝒱.X j ↘ Y) := by
    intro j
    show Etale (𝒱.f j ≫ V.hom)
    let : Etale (𝒱.f j) := 𝒱.map_prop j
    let : Etale V.hom := V.prop
    infer_instance
  let Vj : I → Y.Etale := fun j ↦ by
    let : Etale (𝒱.X j.down ↘ Y) := hVjEt j.down
    exact Scheme.Etale.mk (𝒱.X j.down ↘ Y)
  let fj : ∀ j, Vj j ⟶ V := fun j ↦
    @MorphismProperty.Over.homMk Scheme.{u} (inferInstance : Category.{u, u + 1} Scheme.{u})
      (@Etale : MorphismProperty Scheme.{u}) (⊤ : MorphismProperty Scheme.{u}) Y
      (inferInstance : (⊤ : MorphismProperty Scheme.{u}).IsMultiplicative)
      (Vj j) V (𝒱.f j.down) (by rfl) (by trivial)
  have hcoverV : ∀ y : V.left, ∃ j, y ∈ Set.range (𝒱.f j) :=
    (Scheme.ofArrows_mem_precoverage_iff (P := @Etale.{u})
      (X := 𝒱.X) (f := 𝒱.f)).1 𝒱.mem₀ |>.1
  have hpointsV : (⋃ j, Set.range (fj j).left) = Set.univ :=
    Set.eq_univ_of_forall fun y ↦ by
      obtain ⟨j, x, hx⟩ := hcoverV y
      exact Set.mem_iUnion.mpr ⟨ULift.up j, x, hx⟩
  have hcoverY : Sieve.ofArrows Vj fj ∈ smallEtaleTopology Y V :=
    (Scheme.ofArrows_mem_smallEtaleTopology_iff fj).2 hpointsV
  refine ⟨I, Vj, fj, hcoverY, ?_⟩
  intro j
  let j₀ := j.down
  let Zs : Scheme := Limits.pullback f (𝒱.f j₀ ≫ g)
  let Z : X.Etale := (smallEtaleBaseChange f).obj (Vj j)
  let eJ : Z.left ≅ Zs := by
    show Limits.pullback (𝒱.f j₀ ≫ g) f ≅ Limits.pullback f (𝒱.f j₀ ≫ g)
    exact pullbackSymmetry (𝒱.f j₀ ≫ g) f
  let qj := q j₀
  let ej := e j₀
  let Wj := W j₀
  let aj := a j₀
  let (i : 𝒰'.I₀) : OverClass (𝒰'.X i) X := hOver.over i
  let (i : 𝒰'.I₀) : Etale (𝒰'.X i ↘ X) := hEt i
  let Ui : 𝒰'.I₀ → X.Etale := fun i ↦ by
    let : OverClass (𝒰.X i) X := hOver.over i
    let : Etale (𝒰.X i ↘ X) := hEt i
    exact Etale.mk (𝒰.X i ↘ X)
  let Di : 𝒰'.I₀ → X.Etale := fun i ↦
    Etale.mk (Limits.Sigma.ι Wj i ≫ ej.hom ≫ eJ.inv ≫ Z.hom)
  let ki : ∀ i, Di i ⟶ Z := fun i ↦
    @MorphismProperty.Over.homMk Scheme.{u} (inferInstance : Category.{u, u + 1} Scheme.{u})
      (@Etale : MorphismProperty Scheme.{u}) (⊤ : MorphismProperty Scheme.{u}) X
      (inferInstance : (⊤ : MorphismProperty Scheme.{u}).IsMultiplicative)
      (Di i) Z (Limits.Sigma.ι Wj i ≫ ej.hom ≫ eJ.inv) (by rfl) (by trivial)
  let qEt : Z ⟶ P := (smallEtaleBaseChange f).map (fj j)
  have hleft : qj ≫ eSymm.inv ≫ P.hom = pullback.fst f (𝒱.f j₀ ≫ g) := by
    show qj ≫ (eSymm.inv ≫ pullback.snd V.hom f) = _
    have hs' : eSymm.inv ≫ pullback.snd V.hom f = pullback.fst f V.hom := by
      dsimp [eSymm]
      exact pullbackSymmetry_inv_comp_snd V.hom f
    rw [hs', hqfst j₀]
  have hright : eJ.inv ≫ Z.hom = pullback.fst f (𝒱.f j₀ ≫ g) := by
    show eJ.inv ≫ pullback.snd (Vj j).hom f = _
    dsimp [eJ]
    exact pullbackSymmetry_inv_comp_snd (𝒱.f j₀ ≫ g) f
  have hUf (i : 𝒰'.I₀) : 𝒰'.f i = 𝒰.f i ≫ eSymm.hom := rfl
  let liftArrow' : ∀ i : 𝒰'.I₀, Ui i ⟶ P := fun i ↦ liftArrow i
  let ri : ∀ i, Di i ⟶ Ui i := fun i ↦ by
    let base : (Di i).left ⟶ (Ui i).left := aj i
    exact @MorphismProperty.Over.homMk Scheme.{u}
      (inferInstance : Category.{u, u + 1} Scheme.{u})
      (@Etale : MorphismProperty Scheme.{u}) (⊤ : MorphismProperty Scheme.{u}) X
      (inferInstance : (⊤ : MorphismProperty Scheme.{u}).IsMultiplicative)
      (Di i) (Ui i) base (by
        let : OverClass (𝒰.X i) X := hOver.over i
        have hOvercomp : 𝒰.f i ≫ P.hom = (𝒰.X i ↘ X) := (hOver.isOver_map i).comp_over
        have hbase : base ≫ (Ui i).hom = (Di i).hom := by
          show aj i ≫ (Ui i).hom = Sigma.ι Wj i ≫ ej.hom ≫ eJ.inv ≫ Z.hom
          calc
            aj i ≫ (Ui i).hom = aj i ≫ 𝒰.f i ≫ P.hom := by
              show aj i ≫ (𝒰.X i ↘ X) = _
              rw [← hOvercomp]
              rfl
            _ = aj i ≫ 𝒰'.f i ≫ eSymm.inv ≫ P.hom := by
              have hcancelP : 𝒰.f i ≫ P.hom = (𝒰.f i ≫ eSymm.hom) ≫ eSymm.inv ≫ P.hom := by
                simp
              exact congrArg (fun k ↦ aj i ≫ k) hcancelP
            _ = (Sigma.ι Wj i ≫ ej.hom ≫ qj) ≫ eSymm.inv ≫ P.hom := by
              have hc := congrArg (fun k ↦ k ≫ eSymm.inv ≫ P.hom) (hcomp j₀ i)
              simpa only [aj, Category.assoc] using hc
            _ = Sigma.ι Wj i ≫ ej.hom ≫ eJ.inv ≫ Z.hom := by
              have hbase := hleft.trans hright.symm
              simpa only [Category.assoc] using
                congrArg (fun k ↦ Sigma.ι Wj i ≫ ej.hom ≫ k) hbase
        exact hbase)
      (by trivial)
  have hlift' (i : 𝒰'.I₀) :
      ∃ t : F.obj.obj (op (Ui i)),
        η.hom.app (op (Ui i)) t = G.obj.map (liftArrow' i).op s := by
    simpa [Ui, liftArrow'] using hlift i
  have hri : ∀ i, ri i ≫ liftArrow' i = ki i ≫ qEt := by
    intro i
    apply MorphismProperty.Over.Hom.ext
    let : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun _ _ ↦ inferInstance⟩
    let : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    let : Category.{u, u + 1}
      (MorphismProperty.Over (@Etale : MorphismProperty Scheme.{u}) ⊤ Y) := Y.instCategoryEtale
    show (ri i).left ≫ (liftArrow' i).left = (ki i).left ≫ qEt.left
    dsimp only [qEt, smallEtaleBaseChange]
    show (ri i).left ≫ (liftArrow' i).left =
      (ki i).left ≫
        ((MorphismProperty.Over.pullback
          (@Etale : MorphismProperty Scheme.{u}) ⊤ f).map (fj j)).left
    rw [MorphismProperty.Over.pullback_map_left
      (@Etale : MorphismProperty Scheme.{u}) ⊤ f (fj j)]
    have hInvVj : eJ.inv ≫ pullback.fst (Vj j).hom f = pullback.snd f (Vj j).hom := by
      dsimp [eJ]
      exact pullbackSymmetry_inv_comp_fst (𝒱.f j₀ ≫ g) f
    have hcoord :
        aj i ≫ 𝒰.f i ≫ pullback.fst V.hom f =
          (Sigma.ι Wj i ≫ ej.hom ≫ eJ.inv) ≫
            pullback.fst (Vj j).hom f ≫ (fj j).left := by
      have hsymm : eSymm.hom ≫ pullback.snd f V.hom = pullback.fst V.hom f := by
        dsimp [eSymm]
        exact pullbackSymmetry_hom_comp_snd V.hom f
      calc
        _ = aj i ≫ 𝒰.f i ≫ eSymm.hom ≫ pullback.snd f V.hom := by rw [← hsymm]
        _ = aj i ≫ 𝒰'.f i ≫ pullback.snd f V.hom := by
          rw [hUf i]
          exact congrArg (fun k ↦ k ≫ pullback.snd f V.hom) (Category.assoc _ _ _)
        _ = Sigma.ι Wj i ≫ ej.hom ≫ qj ≫ pullback.snd f V.hom := by
          show (a j₀ i ≫ 𝒰'.f i) ≫ pullback.snd f V.hom =
            Sigma.ι (W j₀) i ≫ (e j₀).hom ≫ q j₀ ≫ pullback.snd f V.hom
          rw [hcomp j₀ i]
          rfl
        _ = Sigma.ι Wj i ≫ ej.hom ≫ pullback.snd f (Vj j).hom ≫ (fj j).left := by
          have hq := congrArg (fun k ↦ (Sigma.ι Wj i ≫ ej.hom) ≫ k) (hqsnd j₀)
          change _ = (Sigma.ι Wj i ≫ ej.hom) ≫
            pullback.snd f (𝒱.f j₀ ≫ V.hom) ≫ 𝒱.f j₀ at hq
          show _ = (Sigma.ι Wj i ≫ ej.hom) ≫
            pullback.snd f (𝒱.f j₀ ≫ V.hom) ≫ 𝒱.f j₀
          simpa only [qj, Category.assoc] using hq
        _ = Sigma.ι Wj i ≫ ej.hom ≫ eJ.inv ≫
            pullback.fst (Vj j).hom f ≫ (fj j).left := by
          rw [← hInvVj]
          rfl
    have hcoordX :
        (ri i).left ≫ (liftArrow' i).left ≫ pullback.snd V.hom f =
          (ki i).left ≫ qEt.left ≫ pullback.snd V.hom f := by
      calc
        _ = (ri i).left ≫ (liftArrow' i).left ≫ P.hom := rfl
        _ = (ri i).left ≫ (Ui i).hom := by rw [MorphismProperty.Over.w (liftArrow' i)]
        _ = (Di i).hom := MorphismProperty.Over.w (ri i)
        _ = (ki i).left ≫ Z.hom := (MorphismProperty.Over.w (ki i)).symm
        _ = (ki i).left ≫ qEt.left ≫ P.hom := by rw [MorphismProperty.Over.w qEt]
    apply pullback.hom_ext
    · have hcompat :
          (pullback.fst (Vj j).hom f ≫ (fj j).left) ≫ V.hom =
            pullback.snd (Vj j).hom f ≫ f := by
        calc
          _ = pullback.fst (Vj j).hom f ≫ ((fj j).left ≫ V.hom) := by simp only [Category.assoc]
          _ = pullback.fst (Vj j).hom f ≫ (Vj j).hom := by rw [MorphismProperty.Over.w (fj j)]
          _ = pullback.snd (Vj j).hom f ≫ f := pullback.condition
      have hlf := pullback.lift_fst (pullback.fst (Vj j).hom f ≫ (fj j).left)
        (pullback.snd (Vj j).hom f) hcompat
      show (aj i ≫ 𝒰.f i) ≫ pullback.fst V.hom f =
        ((Sigma.ι Wj i ≫ ej.hom ≫ eJ.inv) ≫
          pullback.lift (pullback.fst (Vj j).hom f ≫ (fj j).left)
            (pullback.snd (Vj j).hom f) hcompat) ≫ pullback.fst V.hom f
      have hfirst := congrArg (fun k ↦ (Sigma.ι Wj i ≫ ej.hom ≫ eJ.inv) ≫ k) hlf.symm
      calc
        _ = aj i ≫ 𝒰.f i ≫ pullback.fst V.hom f := rfl
        _ = ((Sigma.ι Wj i ≫ ej.hom ≫ eJ.inv) ≫
              pullback.fst (Vj j).hom f) ≫ (fj j).left := hcoord
        _ = (Sigma.ι Wj i ≫ ej.hom ≫ eJ.inv) ≫
              (pullback.fst (Vj j).hom f ≫ (fj j).left) := Category.assoc _ _ _
        _ = (Sigma.ι Wj i ≫ ej.hom ≫ eJ.inv) ≫
              (pullback.lift (pullback.fst (Vj j).hom f ≫ (fj j).left)
                (pullback.snd (Vj j).hom f) hcompat ≫ pullback.fst V.hom f) := hfirst
        _ = ((Sigma.ι Wj i ≫ ej.hom ≫ eJ.inv) ≫
              pullback.lift (pullback.fst (Vj j).hom f ≫ (fj j).left)
                (pullback.snd (Vj j).hom f) hcompat) ≫ pullback.fst V.hom f :=
          (Category.assoc _ _ _).symm
    · exact hcoordX
  have hlocal : ∀ i,
      η.hom.app (op (Di i)) (F.obj.map (ri i).op (Classical.choose (hlift' i))) =
        G.obj.map (ki i).op (G.obj.map qEt.op s) := by
    intro i
    have hn := η.hom.naturality (ri i).op
    have hn' := ConcreteCategory.congr_hom hn (Classical.choose (hlift' i))
    change η.hom.app (op (Di i)) (F.obj.map (ri i).op (Classical.choose (hlift i))) =
      G.obj.map (ri i).op (η.hom.app (op (Ui i)) (Classical.choose (hlift i))) at hn'
    calc
      _ = G.obj.map (ri i).op (η.hom.app (op (Ui i)) (Classical.choose (hlift i))) := hn'
      _ = G.obj.map (ri i).op (G.obj.map (liftArrow' i).op s) := by
            rw [Classical.choose_spec (hlift' i)]
      _ = G.obj.map (ri i ≫ liftArrow' i).op s := by rw [op_comp, Functor.map_comp_apply]
      _ = G.obj.map (ki i ≫ qEt).op s := by rw [hri i]
      _ = G.obj.map (ki i).op (G.obj.map qEt.op s) := by rw [op_comp, Functor.map_comp_apply]
  let sec : ∀ i, F.obj.obj (op (Di i)) := fun i ↦
    F.obj.map (ri i).op (Classical.choose (hlift' i))
  let RZ : Sieve Z := Sieve.ofArrows Di ki
  have hk : ∀ i, (ki i).left = Sigma.ι (fun i ↦ (Di i).left) i ≫ (ej ≪≫ eJ.symm).hom :=
    fun _ ↦ rfl
  have hRZ : RZ ∈ smallEtaleTopology X Z :=
    ofArrows_mem_smallEtaleTopology_of_iso_sigma Di ki (ej ≪≫ eJ.symm) hk
  obtain ⟨t, ht⟩ := exists_section_of_iso_sigma F Di ki (ej ≪≫ eJ.symm) hk sec
  refine ⟨t, G.property.isSeparated Z RZ hRZ _ _ fun T k hk ↦ ?_⟩
  obtain ⟨i, b, rfl⟩ := (Sieve.mem_ofArrows_iff Di ki k).1 hk
  have hn := η.hom.naturality (b ≫ ki i).op
  have hn' := ConcreteCategory.congr_hom hn t
  change η.hom.app (op T) (F.obj.map (b ≫ ki i).op t) =
    G.obj.map (b ≫ ki i).op (η.hom.app (op Z) t) at hn'
  have hb := η.hom.naturality b.op
  have hb' := ConcreteCategory.congr_hom hb (sec i)
  change η.hom.app (op T) (F.obj.map b.op (sec i)) =
    G.obj.map b.op (η.hom.app (op (Di i)) (sec i)) at hb'
  calc
    G.obj.map (b ≫ ki i).op (η.hom.app (op Z) t) =
        η.hom.app (op T) (F.obj.map (b ≫ ki i).op t) := hn'.symm
    _ = η.hom.app (op T) (F.obj.map b.op (sec i)) := by
          rw [op_comp, Functor.map_comp_apply, ht i]
    _ = G.obj.map b.op (η.hom.app (op (Di i)) (sec i)) := hb'
    _ = G.obj.map b.op (G.obj.map (ki i).op (G.obj.map qEt.op s)) := by rw [hlocal i]
    _ = G.obj.map (b ≫ ki i).op (G.obj.map qEt.op s) := by
          rw [op_comp, Functor.map_comp_apply]

/-- Under property (B), direct image of a locally surjective map of sheaves of sets on small
étale sites is again locally surjective. -/
private lemma isLocallySurjective_pushforward_of_hasPropertyB {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : HasPropertyB f) {F G : Sheaf (smallEtaleTopology X) (Type v)} (η : F ⟶ G)
    [Sheaf.IsLocallySurjective η] :
    Presheaf.IsLocallySurjective (smallEtaleTopology Y)
      (((smallEtaleBaseChange f).sheafPushforwardContinuous
        (Type v) (smallEtaleTopology Y) (smallEtaleTopology X)).map η).hom := by
  let b := smallEtaleBaseChange f
  refine ⟨fun {U} s ↦ ?_⟩
  change G.obj.obj (op (b.obj U)) at s
  obtain ⟨I, W, g, hWg, ht⟩ := sectionLifting_of_hasPropertyB f hf η U s
  refine (smallEtaleTopology Y).superset_covering ?_ hWg
  intro V k hk
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff W g k).1 hk
  obtain ⟨t, hti⟩ := ht i
  refine ⟨F.obj.map (b.map a).op t, ?_⟩
  show η.hom.app (op (b.obj V)) (F.obj.map (b.map a).op t) =
    G.obj.map (b.map (a ≫ g i)).op s
  have hn := ConcreteCategory.congr_hom (η.hom.naturality (b.map a).op) t
  change η.hom.app (op (b.obj V)) (F.obj.map (b.map a).op t) =
    G.obj.map (b.map a).op (η.hom.app (op (b.obj (W i))) t) at hn
  rw [hn, hti, b.map_comp, op_comp, Functor.map_comp_apply]

/-- Sheafification is available on the small étale site of a scheme for any coefficient universe
large enough to contain the universe of the scheme: the site has an essentially small dense
subsite, namely the affine objects. -/
private lemma hasSheafify_smallEtaleTopology (X : Scheme.{u}) [UnivLE.{u, v}] :
    HasSheafify X.smallEtaleTopology (Type v) := by
  let : EssentiallySmall.{v} X.AffineEtale :=
    (essentiallySmall_congr (equivSmallModel.{u} X.AffineEtale)).2 inferInstance
  let : HasSheafify (AffineEtale.topology X) (Type v) := hasSheafifyEssentiallySmallSite _ _
  let : ((AffineEtale.Spec X).sheafPushforwardContinuous (Type v)
      (AffineEtale.topology X) X.smallEtaleTopology).IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _
  exact Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (AffineEtale.topology X) X.smallEtaleTopology (AffineEtale.Spec X) (A := Type v)

/-- **Stacks Project, Tag 04DO.** Let `f : X ⟶ Y` be a morphism of schemes with property (B).
Then direct image along the induced morphism of small étale sites transforms surjections of
sheaves of sets into surjections. -/
@[stacks 04DO]
theorem smallEtalePushforward_preservesEpimorphisms_of_hasPropertyB {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : HasPropertyB f) :
    ((smallEtaleBaseChange f).sheafPushforwardContinuous
      (Type v) (smallEtaleTopology Y) (smallEtaleTopology X)).PreservesEpimorphisms := by
  classical
  by_cases huv : UnivLE.{u, v}
  · let := huv
    let : HasSheafify X.smallEtaleTopology (Type v) := hasSheafify_smallEtaleTopology X
    refine ⟨fun {F G} η hη ↦ ?_⟩
    have : Sheaf.IsLocallySurjective η := (Sheaf.isLocallySurjective_iff_epi η).2 hη
    have := isLocallySurjective_pushforward_of_hasPropertyB f hf η
    exact Sheaf.epi_of_isLocallySurjective _
  · refine ⟨fun {F G} η hη ↦ ⟨fun {H} α β h ↦ ?_⟩⟩
    ext U s
    by_contra hne
    exact huv (univLE_of_ne_sections H U.unop _ _ hne)

end Stacks.EtaleCohomology

end
