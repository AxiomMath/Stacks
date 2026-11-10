module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Fpqc descent for morphisms of algebraic spaces (Stacks 04P2)

An fpqc covering `{T i ⟶ T}` of algebraic spaces over `S` is an effective epimorphism for
morphisms into a fixed algebraic space `Z`: a family of morphisms `T i ⟶ Z` agreeing on the
fibre products `T i ×_T T j` descends uniquely to `T ⟶ Z`, so that
`Mor(T, Z) ⟶ ∏ i, Mor(T i, Z) ⇉ ∏ (i, j), Mor(T i ×_T T j, Z)` is an equalizer. This is
**Stacks 04P2**.

The one input is **Stacks 0APL**, Gabber's theorem that an algebraic space satisfies the sheaf
condition for the fpqc topology and not merely for the fppf topology of its defining site; of it
the source says that it "is the key fact and we encourage the reader to skip the rest of the
proof which is formal".

That formal part runs as follows. A section of `Z` over an object `T` of the site is produced by
refining `T` first by its affine opens and then, on each of those, by the finite affine fpqc
family that the fpqc condition supplies; composing the two gives an fpqc covering of `T` by
affine objects of the site, each member of which factors through some `T i`, so the compatible
family produces a compatible family of sections of `Z` and the fpqc sheaf condition glues it.
Uniqueness is the separatedness half of the same sheaf condition, applied after base change
along an arbitrary `T' ⟶ T`. The sections so obtained are natural, which is uniqueness again,
and assemble into the descended morphism.

Only the *target* `Z` is ever asked to be an fpqc sheaf, so the formal part is stated that way,
and Stacks 0APL enters only to specialize it to every algebraic space. That distinction keeps
the result available for a *representable* target without Stacks 0APL, the fpqc topology of the
site being subcanonical.

## Main results

* `AlgebraicGeometry.Space.existsUnique_desc_of_fpqcCovering`: **Stacks 04P2** — the equalizer
  diagram for morphisms into an algebraic space along an fpqc covering of algebraic spaces.
* `AlgebraicGeometry.Space.existsUnique_desc_of_fpqcCovering_of_target_isSheaf_fpqc`: the same
  conclusion asking only that the target satisfy the fpqc sheaf condition.
* `AlgebraicGeometry.Space.existsUnique_desc_of_fpqcCovering_of_isSheaf_fpqc`: the same
  conclusion from the fpqc sheaf condition for every algebraic space, that is, from Stacks 0APL
  taken as a hypothesis.

## Implementation notes

The passage from an affine open of an object of the site to an object of the site is supplied by
the size API of `AlgebraicGeometry.Scheme.size`, since an open subscheme of a scheme below the
site's cutoff is again below it.

## References

* [Stacks Project, Tag 04P2](https://stacks.math.columbia.edu/tag/04P2)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

private theorem contains_affineOpen
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj T).affineOpens) :
    B.Contains V.1.toScheme := by
  change V.1.toScheme.size < B.cutoff
  exact (Scheme.size_coe_opens_le _ V.1).trans_lt T.left.2

private noncomputable def object_open
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj T).affineOpens) :
    BigFppfOver B S hS := by
  let m : B.obj (contains_affineOpen B S hS T V) ⟶ T.left := B.inclusion.preimage V.1.ι
  exact Over.mk (m ≫ T.hom)

private noncomputable def object_open_inclusion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj T).affineOpens) :
    object_open B S hS T V ⟶ T := by
  let m : B.inclusion.obj (B.obj (contains_affineOpen B S hS T V)) ⟶ B.inclusion.obj T.left := V.1.ι
  exact Over.homMk (B.inclusion.preimage m) (by simp [object_open, m])

private theorem object_open_map_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj T).affineOpens) :
    (BigFppfOver.toScheme B S hS).map
        (object_open_inclusion B S hS T V) = V.1.ι := by
  let vhom : B.inclusion.obj (B.obj (contains_affineOpen B S hS T V)) ⟶
    B.inclusion.obj T.left := V.1.ι
  change B.inclusion.map (B.inclusion.preimage vhom) = vhom
  exact B.inclusion.map_preimage vhom

private theorem ofArrows_object_open_mem_zariskiPrecoverage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS) :
    Presieve.ofArrows
        (fun V : ((BigFppfOver.toScheme B S hS).obj T).affineOpens =>
          (BigFppfOver.toScheme B S hS).obj (object_open B S hS T V))
        (fun V => (BigFppfOver.toScheme B S hS).map (object_open_inclusion B S hS T V)) ∈
      Scheme.zariskiPrecoverage ((BigFppfOver.toScheme B S hS).obj T) := by
  let Q := BigFppfOver.toScheme B S hS
  rw [Scheme.zariskiPrecoverage,
    Scheme.ofArrows_mem_precoverage_iff
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})]
  refine ⟨fun x => ?_, fun V => ?_⟩
  · obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      (Q.obj T).isBasis_affineOpens.mem_nhds_iff.mp
        ((⊤ : TopologicalSpace.Opens (Q.obj T)).isOpen.mem_nhds (by simp))
    refine ⟨⟨V, hV⟩, ⟨x, hxV⟩, ?_⟩
    change (Q.map (object_open_inclusion B S hS T ⟨V, hV⟩)).base ⟨x, hxV⟩ = x
    rw [object_open_map_eq]
    rfl
  · rw [object_open_map_eq]
    exact inferInstanceAs (AlgebraicGeometry.IsOpenImmersion V.1.ι)

/-- Precomposing a lift of `yoneda.map w ≫ s` with `yoneda.map e` lifts `yoneda.map (e ≫ w) ≫ s`. -/
private theorem yoneda_map_comp_lift_comp {C : Type*} [Category C] {F G : Cᵒᵖ ⥤ Type _}
    {R U T : C} (e : R ⟶ U) (w : U ⟶ T) (l : yoneda.obj U ⟶ F) (φ : F ⟶ G)
    (s : yoneda.obj T ⟶ G) (hl : l ≫ φ = yoneda.map w ≫ s) :
    (yoneda.map e ≫ l) ≫ φ = yoneda.map (e ≫ w) ≫ s := by
  rw [Category.assoc, hl, Functor.map_comp, Category.assoc]

private theorem compatible_sections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : I → AlgebraicSpaces B S hS}
    {Y Z : AlgebraicSpaces B S hS}
    (f : ∀ i, X i ⟶ Y) (g : ∀ i, X i ⟶ Z)
    (hg : ∀ i j,
      (ObjectProperty.homMk (pullback.fst (f i).hom (f j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (f i) (f j) ⟶ X i) ≫ g i =
      (ObjectProperty.homMk (pullback.snd (f i).hom (f j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (f i) (f j) ⟶ X j) ≫ g j)
    {T : BigFppfOver B S hS} (i j : I)
    (a : yoneda.obj T ⟶ (X i).obj) (b : yoneda.obj T ⟶ (X j).obj)
    (hab : a ≫ (f i).hom = b ≫ (f j).hom) :
    yonedaEquiv (a ≫ (g i).hom) = yonedaEquiv (b ≫ (g j).hom) := by
  let Tsp : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let aa : Tsp ⟶ X i := ObjectProperty.homMk a
  let bb : Tsp ⟶ X j := ObjectProperty.homMk b
  have hab' : aa ≫ f i = bb ≫ f j := by
    apply ObjectProperty.hom_ext
    exact hab
  let P := AlgebraicSpaces.fiberProduct B S hS (f i) (f j)
  let p₁ : P ⟶ X i := ObjectProperty.homMk (pullback.fst (f i).hom (f j).hom)
  let p₂ : P ⟶ X j := ObjectProperty.homMk (pullback.snd (f i).hom (f j).hom)
  have hP := AlgebraicSpaces.isPullback_fiberProduct B S hS (f i) (f j)
  let l : Tsp ⟶ P := hP.lift aa bb hab'
  have hcomp : aa ≫ g i = bb ≫ g j := by
    calc
      aa ≫ g i = (l ≫ p₁) ≫ g i := by rw [hP.lift_fst]
      _ = l ≫ (p₁ ≫ g i) := Category.assoc _ _ _
      _ = l ≫ (p₂ ≫ g j) := congrArg (fun q => l ≫ q) (hg i j)
      _ = (l ≫ p₂) ≫ g j := (Category.assoc _ _ _).symm
      _ = bb ≫ g j := by rw [hP.lift_snd]
  exact congrArg yonedaEquiv
    (by simpa [aa, bb] using congrArg (fun q : Tsp ⟶ Z => q.hom) hcomp)

private theorem exists_cover_lift
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : I → AlgebraicSpaces B S hS} {Y : AlgebraicSpaces B S hS}
    (f : ∀ i, X i ⟶ Y) (hf : IsFpqcCovering B S hS (fun i => (f i).hom))
    (T : BigFppfOver B S hS) (y : Y.obj.obj (Opposite.op T)) :
    ∃ W : PreZeroHypercover.{u + 1} T,
      W.presieve₀ ∈ (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)) T ∧
      ∀ p, ∃ (i : I) (l : yoneda.obj (W.X p) ⟶ (X i).obj),
        l ≫ (f i).hom = yoneda.map (W.f p) ≫ yonedaEquiv.symm y := by
  classical
  let Q := BigFppfOver.toScheme B S hS
  let Tsch := Q.obj T
  let J := Tsch.affineOpens
  let Wobj (V : J) := object_open B S hS T V
  let A := BigAffineFppf.inclusion B S hS
  let Waff (V : J) : BigAffineFppf B S hS := ⟨Wobj V, V.property⟩
  let O : PreZeroHypercover T := {
    I₀ := J
    X := Wobj
    f := object_open_inclusion B S hS T
  }
  let hV (V : J) : yoneda.obj (A.obj (Waff V)) ⟶ Y.obj :=
    yoneda.map (O.f V) ≫ yonedaEquiv.symm y
  have hlocal (V : J) := hf.2 (Waff V) (hV V)
  choose E hEfinite hEcover hEfactor using hlocal
  let W : PreZeroHypercover T := {
    I₀ := Σ V : J, (E V).I₀
    X p := A.obj ((E p.1).X p.2)
    f p := A.map ((E p.1).f p.2) ≫ O.f p.1
  }
  refine ⟨W, ?_, fun p => ?_⟩
  · rw [Scheme.fpqcPrecoverage.mem_comap_iff]
    let F := BigAffineFppf.toScheme B S hS
    have hEcover' (V : J) :
        Presieve.ofArrows (fun j => F.obj ((E V).X j))
          (fun j => F.map ((E V).f j)) ∈
            Scheme.fpqcPrecoverage (Q.obj (O.X V)) := by
      have hEV : Presieve.map F (E V).presieve₀ ∈
          Scheme.fpqcPrecoverage (Q.obj (O.X V)) := by
        convert hEcover V using 1 <;> rfl
      simpa [F, PreZeroHypercover.presieve₀_map] using hEV
    have hcomp :
        Presieve.ofArrows (fun p : Σ V : J, (E V).I₀ => F.obj ((E p.1).X p.2))
          (fun p => F.map ((E p.1).f p.2) ≫ Q.map (O.f p.1)) ∈
            Scheme.fpqcPrecoverage Tsch :=
      Precoverage.comp_mem_coverings (J := Scheme.fpqcPrecoverage)
        (f := fun V : J => Q.map (O.f V))
        (Scheme.zariskiPrecoverage_le_fpqcPrecoverage Tsch
          (ofArrows_object_open_mem_zariskiPrecoverage B S hS T))
        (g := fun V j => F.map ((E V).f j)) hEcover'
    simpa [W, F, A, Q, Tsch, BigAffineFppf.toScheme,
      BigFppfOver.toScheme, BigFppfOver.forget,
      PreZeroHypercover.presieve₀_map,
      Functor.map_comp] using hcomp
  · obtain ⟨i, l, hl⟩ := hEfactor p.1 p.2
    refine ⟨i, l, ?_⟩
    dsimp [W, hV, O] at hl ⊢
    simpa [A, Functor.map_comp, Category.assoc] using hl

private theorem map_eq_of_mem_cover
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : I → AlgebraicSpaces B S hS}
    {Y Z : AlgebraicSpaces B S hS}
    (hZ : Presieve.IsSheaf
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck Z.obj)
    (f : ∀ i, X i ⟶ Y) (g : ∀ i, X i ⟶ Z)
    (hg : ∀ i j,
      (ObjectProperty.homMk (pullback.fst (f i).hom (f j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (f i) (f j) ⟶ X i) ≫ g i =
      (ObjectProperty.homMk (pullback.snd (f i).hom (f j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (f i) (f j) ⟶ X j) ≫ g j)
    {T : BigFppfOver B S hS} (y : Y.obj.obj (Opposite.op T)) (W : PreZeroHypercover.{u + 1} T)
    (hW : W.presieve₀ ∈ (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)) T)
    (ix : W.I₀ → I) (lift : ∀ p, yoneda.obj (W.X p) ⟶ (X (ix p)).obj)
    (hlift : ∀ p, lift p ≫ (f (ix p)).hom = yoneda.map (W.f p) ≫ yonedaEquiv.symm y)
    (z : Z.obj.obj (Opposite.op T))
    (hz : ∀ p, Z.obj.map (W.f p).op z = yonedaEquiv (lift p ≫ (g (ix p)).hom))
    {T' : BigFppfOver B S hS} (q : T' ⟶ T) (i : I) (b : yoneda.obj T' ⟶ (X i).obj)
    (hbi : b ≫ (f i).hom = yoneda.map q ≫ yonedaEquiv.symm y) :
    Z.obj.map q.op z = yonedaEquiv (b ≫ (g i).hom) := by
  let P (p : W.I₀) := pullback (W.f p) q
  let rT (p : W.I₀) : P p ⟶ T' := pullback.snd (W.f p) q
  let rW (p : W.I₀) : P p ⟶ W.X p := pullback.fst (W.f p) q
  have hPB (p : W.I₀) : IsPullback (rT p) (rW p) q (W.f p) :=
    (IsPullback.of_hasPullback (W.f p) q).flip
  have hpullsheaf : (Presieve.ofArrows P rT).IsSheafFor Z.obj :=
    Presieve.IsSheaf.isSheafFor_of_mem_precoverage hZ
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).mem_coverings_of_isPullback
        W.f hW q rT rW hPB)
  apply hpullsheaf.isSeparatedFor.ext
  intro R r hr
  let p : W.I₀ := hr.idx
  have hYlocal :
      (yoneda.map (rW p) ≫ lift p) ≫ (f (ix p)).hom =
        (yoneda.map (rT p) ≫ b) ≫ (f i).hom := by
    rw [yoneda_map_comp_lift_comp _ _ _ _ _ (hlift p), ← hPB p |>.w,
      yoneda_map_comp_lift_comp _ _ _ _ _ hbi]
  have hcanon : Z.obj.map (rT p).op (Z.obj.map q.op z) =
      Z.obj.map (rT p).op (yonedaEquiv (b ≫ (g i).hom)) := by
    calc
      Z.obj.map (rT p).op (Z.obj.map q.op z) =
        Z.obj.map (rW p).op (Z.obj.map (W.f p).op z) := by
          rw [← Functor.map_comp_apply, ← Functor.map_comp_apply,
            ← op_comp, ← op_comp, hPB p |>.w]
      _ = yonedaEquiv (yoneda.map (rW p) ≫ (lift p ≫ (g (ix p)).hom)) := by
          rw [hz p, ← yonedaEquiv_naturality]
      _ = yonedaEquiv (yoneda.map (rT p) ≫ (b ≫ (g i).hom)) := by
          simpa [Category.assoc] using compatible_sections B S hS f g hg
            (ix p) i (yoneda.map (rW p) ≫ lift p) (yoneda.map (rT p) ≫ b) hYlocal
      _ = Z.obj.map (rT p).op (yonedaEquiv (b ≫ (g i).hom)) := by
          rw [← yonedaEquiv_naturality]
  rw [Presieve.ofArrows.eq_eqToHom_comp_hom_idx hr]
  simp only [op_comp, Functor.map_comp_apply]
  exact congrArg (Z.obj.map (eqToHom (Presieve.ofArrows.obj_idx hr).symm).op) hcanon

private theorem existsUnique_localSection
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : I → AlgebraicSpaces B S hS}
    {Y Z : AlgebraicSpaces B S hS}
    (hZfpqc : Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) Z.obj)
    (f : ∀ i, X i ⟶ Y)
    (hf : IsFpqcCovering B S hS (fun i => (f i).hom))
    (g : ∀ i, X i ⟶ Z)
    (hg : ∀ i j,
      (ObjectProperty.homMk (pullback.fst (f i).hom (f j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (f i) (f j) ⟶ X i) ≫ g i =
      (ObjectProperty.homMk (pullback.snd (f i).hom (f j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (f i) (f j) ⟶ X j) ≫ g j)
    (T : BigFppfOver B S hS) (y : Y.obj.obj (Opposite.op T)) :
    ∃! z : Z.obj.obj (Opposite.op T),
      ∀ (T' : BigFppfOver B S hS) (q : T' ⟶ T) (i : I)
        (b : yoneda.obj T' ⟶ (X i).obj),
        b ≫ (f i).hom = yoneda.map q ≫ yonedaEquiv.symm y →
        Z.obj.map q.op z = yonedaEquiv (b ≫ (g i).hom) := by
  obtain ⟨W, hW, hWlift⟩ := exists_cover_lift B S hS f hf T y
  choose ix lift hlift using hWlift
  have hZ : Presieve.IsSheaf
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck Z.obj :=
    (isSheaf_iff_isSheaf_of_type _ Z.obj).mp hZfpqc
  have hWsheaf : W.presieve₀.IsSheafFor Z.obj :=
    Presieve.IsSheaf.isSheafFor_of_mem_precoverage hZ hW
  let x (p : W.I₀) : Z.obj.obj (Opposite.op (W.X p)) :=
    yonedaEquiv (lift p ≫ (g (ix p)).hom)
  have hx : Presieve.Arrows.Compatible Z.obj W.f x := by
    intro i j R e₁ e₂ he
    have hcomp := compatible_sections B S hS f g hg
      (ix i) (ix j) (yoneda.map e₁ ≫ lift i) (yoneda.map e₂ ≫ lift j)
    have heY :
        (yoneda.map e₁ ≫ lift i) ≫ (f (ix i)).hom =
          (yoneda.map e₂ ≫ lift j) ≫ (f (ix j)).hom := by
      rw [yoneda_map_comp_lift_comp _ _ _ _ _ (hlift i), he,
        yoneda_map_comp_lift_comp _ _ _ _ _ (hlift j)]
    calc
      Z.obj.map e₁.op (x i) =
          yonedaEquiv (yoneda.map e₁ ≫ (lift i ≫ (g (ix i)).hom)) := by
        rw [← yonedaEquiv_naturality]
      _ = yonedaEquiv (yoneda.map e₂ ≫ (lift j ≫ (g (ix j)).hom)) := by
        simpa [Category.assoc] using hcomp heY
      _ = Z.obj.map e₂.op (x j) := by
        rw [← yonedaEquiv_naturality]
  rw [Presieve.isSheafFor_arrows_iff] at hWsheaf
  obtain ⟨z, hz, hzu⟩ := hWsheaf x hx
  exact ⟨z, fun _ q i b hbi => map_eq_of_mem_cover B S hS hZ f g hg y W hW ix lift hlift z hz
      q i b hbi,
    fun z' hz' => hzu z' fun p => hz' (W.X p) (W.f p) (ix p) (lift p) (hlift p)⟩

private theorem localSection_map
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : I → AlgebraicSpaces B S hS} {Y Z : AlgebraicSpaces B S hS}
    (f : ∀ i, X i ⟶ Y) (g : ∀ i, X i ⟶ Z)
    {T₀ T₁ : BigFppfOver B S hS} (q : T₀ ⟶ T₁) (y : Y.obj.obj (Opposite.op T₁))
    (z : Z.obj.obj (Opposite.op T₁))
    (hz : ∀ (T' : BigFppfOver B S hS) (r : T' ⟶ T₁) (i : I)
      (b : yoneda.obj T' ⟶ (X i).obj),
      b ≫ (f i).hom = yoneda.map r ≫ yonedaEquiv.symm y →
      Z.obj.map r.op z = yonedaEquiv (b ≫ (g i).hom))
    (T' : BigFppfOver B S hS) (r : T' ⟶ T₀) (i : I) (b : yoneda.obj T' ⟶ (X i).obj)
    (hb : b ≫ (f i).hom = yoneda.map r ≫ yonedaEquiv.symm (Y.obj.map q.op y)) :
    Z.obj.map r.op (Z.obj.map q.op z) = yonedaEquiv (b ≫ (g i).hom) := by
  have hsymm : yonedaEquiv.symm (Y.obj.map q.op y) =
      yoneda.map q ≫ yonedaEquiv.symm y := by
    apply yonedaEquiv.injective
    simpa using yonedaEquiv_naturality (yonedaEquiv.symm y) q
  have hloc := hz T' (r ≫ q) i b (by
    rw [hb, hsymm]
    simp [Functor.map_comp, Category.assoc])
  simpa only [op_comp, Functor.map_comp_apply] using hloc

private theorem localSection_of_comp_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : I → AlgebraicSpaces B S hS} {Y Z : AlgebraicSpaces B S hS}
    (f : ∀ i, X i ⟶ Y) (g : ∀ i, X i ⟶ Z) (h : Y ⟶ Z) (hh : ∀ i, f i ≫ h = g i)
    (T : BigFppfOver B S hS) (y : Y.obj.obj (Opposite.op T))
    (T' : BigFppfOver B S hS) (q : T' ⟶ T) (i : I) (b : yoneda.obj T' ⟶ (X i).obj)
    (hbi : b ≫ (f i).hom = yoneda.map q ≫ yonedaEquiv.symm y) :
    Z.obj.map q.op (h.hom.app (Opposite.op T) y) = yonedaEquiv (b ≫ (g i).hom) := by
  have hsection : yonedaEquiv (b ≫ (f i).hom) = Y.obj.map q.op y := by
    rw [hbi, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
  calc
    Z.obj.map q.op (h.hom.app (Opposite.op T) y) =
        h.hom.app (Opposite.op T') (Y.obj.map q.op y) := by
          rw [NatTrans.naturality_apply]
    _ = h.hom.app (Opposite.op T') (yonedaEquiv (b ≫ (f i).hom)) := by
          rw [hsection]
    _ = yonedaEquiv (b ≫ (g i).hom) := by
          rw [← yonedaEquiv_comp]
          apply congrArg yonedaEquiv
          simpa [Category.assoc] using
            congrArg (fun k => b ≫ k) (congrArg (fun k => k.hom) (hh i))

/-- **Stacks 04P2** for a target satisfying the fpqc sheaf condition. A compatible family of
morphisms from the members of an fpqc covering of algebraic spaces over `S` to an algebraic
space `Z` descends uniquely to the target of the covering, provided `Z` satisfies the sheaf
condition for the fpqc topology of the site.

Only the target is asked for anything beyond being an algebraic space, which is all the proof
uses; Stacks 0APL is what supplies `hZfpqc` for an arbitrary algebraic space, and the fpqc
topology of the site being subcanonical is what supplies it for a representable one. -/
public theorem existsUnique_desc_of_fpqcCovering_of_target_isSheaf_fpqc
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : I → AlgebraicSpaces B S hS}
    {Y : AlgebraicSpaces B S hS}
    (f : ∀ i, X i ⟶ Y)
    (hf : IsFpqcCovering B S hS (fun i => (f i).hom))
    (Z : AlgebraicSpaces B S hS)
    (hZfpqc : Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) Z.obj)
    (g : ∀ i, X i ⟶ Z)
    (hg : ∀ i j,
      (ObjectProperty.homMk (pullback.fst (f i).hom (f j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (f i) (f j) ⟶ X i) ≫ g i =
      (ObjectProperty.homMk (pullback.snd (f i).hom (f j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (f i) (f j) ⟶ X j) ≫ g j) :
    ∃! h : Y ⟶ Z, ∀ i, f i ≫ h = g i := by
  classical
  let localDesc := existsUnique_localSection B S hS hZfpqc f hf g hg
  let sectionAt (T : BigFppfOver B S hS)
      (y : Y.obj.obj (Opposite.op T)) : Z.obj.obj (Opposite.op T) :=
    (localDesc T y).choose
  let η : Y.obj ⟶ Z.obj := {
    app := fun T => TypeCat.ofHom (sectionAt T.unop)
    naturality := by
      intro T' T q
      apply ConcreteCategory.ext
      ext y
      exact ((localDesc T.unop (Y.obj.map q y)).choose_spec.2 _
        (localSection_map B S hS f g q.unop y (sectionAt T'.unop y)
          (localDesc T'.unop y).choose_spec.1)).symm
  }
  have hηapp (T : BigFppfOver B S hS)
      (y : Y.obj.obj (Opposite.op T)) : η.app (Opposite.op T) y = sectionAt T y := rfl
  let h : Y ⟶ Z := ObjectProperty.homMk η
  have hfactor (i : I) : f i ≫ h = g i := by
    apply ObjectProperty.hom_ext
    ext T x
    cases T with
    | op T =>
      let b : yoneda.obj T ⟶ (X i).obj := yonedaEquiv.symm x
      let y := (f i).hom.app (Opposite.op T) x
      have hb : b ≫ (f i).hom = yonedaEquiv.symm y := by
        apply yonedaEquiv.injective
        rw [yonedaEquiv_comp]
        simp [b, y]
      have hl := (localDesc T y).choose_spec.1 T (𝟙 T) i b (by simpa using hb)
      change η.app (Opposite.op T) y = (g i).hom.app (Opposite.op T) x
      rw [hηapp]
      have hglocal : yonedaEquiv (b ≫ (g i).hom) =
          (g i).hom.app (Opposite.op T) x := by
        simpa [b] using yonedaEquiv_comp (yonedaEquiv.symm x) (g i).hom
      simpa using hl.trans hglocal
  refine ⟨h, hfactor, fun h' hh' => ?_⟩
  apply ObjectProperty.hom_ext
  ext T y
  cases T with
  | op T =>
    change h'.hom.app (Opposite.op T) y = η.app (Opposite.op T) y
    rw [hηapp]
    exact (localDesc T y).choose_spec.2 _ (localSection_of_comp_eq B S hS f g h' hh' T y)

/-- **Stacks 04P2** from **Stacks 0APL** taken as a hypothesis. A compatible family of
morphisms from the members of an fpqc covering of algebraic spaces over `S` to an algebraic
space `Z` descends uniquely to the target of the covering, provided every algebraic space over
`S` satisfies the sheaf condition for the fpqc topology.

The hypothesis `hfpqc` is exactly Stacks 0APL (Gabber), proved in
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc`; discharging it there gives
`AlgebraicGeometry.Space.existsUnique_desc_of_fpqcCovering`. -/
public theorem existsUnique_desc_of_fpqcCovering_of_isSheaf_fpqc
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hfpqc : ∀ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS F →
      Presheaf.IsSheaf
        ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) F)
    {I : Type v} {X : I → AlgebraicSpaces B S hS}
    {Y : AlgebraicSpaces B S hS}
    (f : ∀ i, X i ⟶ Y)
    (hf : IsFpqcCovering B S hS (fun i => (f i).hom))
    (Z : AlgebraicSpaces B S hS)
    (g : ∀ i, X i ⟶ Z)
    (hg : ∀ i j,
      (ObjectProperty.homMk (pullback.fst (f i).hom (f j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (f i) (f j) ⟶ X i) ≫ g i =
      (ObjectProperty.homMk (pullback.snd (f i).hom (f j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (f i) (f j) ⟶ X j) ≫ g j) :
    ∃! h : Y ⟶ Z, ∀ i, f i ≫ h = g i :=
  existsUnique_desc_of_fpqcCovering_of_target_isSheaf_fpqc B S hS f hf Z
    (hfpqc Z.obj Z.property) g hg

/-- **Stacks 04P2.** For an fpqc covering `{X i ⟶ Y}` of algebraic spaces over `S` and an
algebraic space `Z` over `S`, the diagram
`Mor(Y, Z) ⟶ ∏ i, Mor(X i, Z) ⇉ ∏ (i, j), Mor(X i ×_Y X j, Z)` is an equalizer: a family of
morphisms `X i ⟶ Z` agreeing on the fibre products `X i ×_Y X j` descends uniquely to `Y ⟶ Z`.

The input is Stacks 0APL, that an algebraic space is a sheaf for the fpqc topology; the rest is
formal. -/
@[stacks 04P2]
public theorem existsUnique_desc_of_fpqcCovering
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : I → AlgebraicSpaces B S hS}
    {Y : AlgebraicSpaces B S hS}
    (f : ∀ i, X i ⟶ Y)
    (hf : IsFpqcCovering B S hS (fun i => (f i).hom))
    (Z : AlgebraicSpaces B S hS)
    (g : ∀ i, X i ⟶ Z)
    (hg : ∀ i j,
      (ObjectProperty.homMk (pullback.fst (f i).hom (f j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (f i) (f j) ⟶ X i) ≫ g i =
      (ObjectProperty.homMk (pullback.snd (f i).hom (f j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (f i) (f j) ⟶ X j) ≫ g j) :
    ∃! h : Y ⟶ Z, ∀ i, f i ≫ h = g i :=
  existsUnique_desc_of_fpqcCovering_of_isSheaf_fpqc B S hS
    (fun _ hF => IsAlgebraicSpace.isSheaf_fpqc hF) f hf Z g hg

end AlgebraicGeometry.Space

end
