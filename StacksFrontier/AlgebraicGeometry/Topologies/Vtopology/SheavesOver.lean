module

public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Sites.CoproductSheafCondition
public import Mathlib.CategoryTheory.Sites.Preserves
public import StacksFrontier.AlgebraicGeometry.Limits.CoproductUniversal
public import StacksFrontier.AlgebraicGeometry.Topologies.V.CoveringsOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Vtopology.Sheaves
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Recognizing sheaves for the V topology on the schemes over a base

A functor on `Sch/S` is a sheaf for the V topology exactly when it is a sheaf for the Zariski
coverings and satisfies the sheaf condition for the families whose underlying family of schemes is
a standard V covering of an affine scheme.  Under the first condition the second may be tested on
the families consisting of a single arrow.  This is the relative form, for the schemes over a
base, of Stacks 0ETM.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.IsZariskiCoverSheafOver`: the sheaf condition for the
  families of `Sch/S` which an open covering of the underlying scheme of an object lifts to.
* `AlgebraicGeometry.ExtendingFunctors.IsStandardVSheafOver`: the sheaf condition for the families
  of `Sch/S` whose underlying family of schemes is a standard V covering of an affine scheme.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.isVSheafOver_iff_zariski_and_standard` reduces the V sheaf
  condition on `Sch/S` to the Zariski sheaf condition together with the standard V coverings of
  the affine objects.
* `AlgebraicGeometry.ExtendingFunctors.isStandardVSheafOver_iff_singleton` reduces the standard V
  sheaf condition on `Sch/S` to the single-arrow case.

## Implementation notes

Every object and every morphism occurring in a covering of an object `Y` of `Sch/S` lies over `Y`,
hence over `S`, so no covering is constructed in `Sch/S`: a covering family of schemes over
`Y.left` is lifted to `Sch/S` by `AlgebraicGeometry.ExtendingFunctors.overLift`, whose underlying
family of schemes is the given one.  In particular the fibre products appearing in the argument
are the fibre products of the underlying schemes, so the base change statements for V coverings
and for standard V coverings apply unchanged, and every equation between morphisms of `Sch/S` is
the corresponding equation between the underlying morphisms of schemes.

The reduction to the single-arrow case is the one place where the slice is not bookkeeping: it
rewrites a finite family as the single arrow out of the coproduct of its members, which asks for
the coproducts of `Sch/S` to be universal.  They are, because `Over.forget S` creates colimits
and preserves pullbacks, so a coproduct cofan of `Sch/S` is van Kampen as soon as its image in
`Scheme` is.

## References

* [Stacks Project, Tag 0ETM](https://stacks.math.columbia.edu/tag/0ETM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u v

namespace AlgebraicGeometry.ExtendingFunctors

variable {S : Scheme.{u}}

/-! ### The two conditions -/

/-- The Zariski sheaf condition on `Sch/S`: for every object `X` of `Sch/S` and every open
covering of the scheme `X.left`, the family of objects of `Sch/S` over `X` that it lifts to
satisfies the sheaf condition. -/
def IsZariskiCoverSheafOver (G : (Over S)ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (X : Over S) (𝒰 : X.left.OpenCover.{v}),
    (Presieve.ofArrows (fun i ↦ overLift X (𝒰.f i))
      (fun i ↦ overLiftι X (𝒰.f i))).IsSheafFor G

/-- The sheaf condition on `Sch/S` for the families of morphisms into an affine object whose
underlying family of morphisms of schemes is a standard V covering. -/
def IsStandardVSheafOver (G : (Over S)ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (X : Over S) [IsAffine X.left] (I : Type v) [Finite I] (Y : I → Over S)
    [∀ i, IsAffine (Y i).left] (f : ∀ i, Y i ⟶ X),
    IsStandardVCovering (fun i ↦ (Y i).left) (fun i ↦ (f i).left) →
      (Presieve.ofArrows Y f).IsSheafFor G

/-- The presieve of a family of morphisms of `Sch/S` and the presieve of the family obtained by
lifting the underlying morphisms of schemes generate the same sieve, the two families differing
only by an isomorphism over the target.  Either sheaf condition therefore gives the other. -/
theorem isSheafFor_ofArrows_iff_overLift {G : (Over S)ᵒᵖ ⥤ Type w} {X : Over S} {ι : Type v}
    (Y : ι → Over S) (f : ∀ i, Y i ⟶ X) :
    (Presieve.ofArrows (fun i ↦ overLift X (f i).left)
        (fun i ↦ overLiftι X (f i).left)).IsSheafFor G ↔
      (Presieve.ofArrows Y f).IsSheafFor G := by
  have hgen : Sieve.generate (Presieve.ofArrows (fun i ↦ overLift X (f i).left)
      (fun i ↦ overLiftι X (f i).left)) = Sieve.generate (Presieve.ofArrows Y f) := by
    apply le_antisymm
    · rw [Sieve.generate_le_iff]
      rintro W g ⟨i⟩
      refine ⟨_, (overLiftIso (f i)).hom, f i, Presieve.ofArrows.mk i, ?_⟩
      apply Over.OverMorphism.ext
      simp [overLiftIso]
    · rw [Sieve.generate_le_iff]
      rintro W g ⟨i⟩
      refine ⟨_, (overLiftIso (f i)).inv, overLiftι X (f i).left,
        Presieve.ofArrows.mk i, ?_⟩
      apply Over.OverMorphism.ext
      simp [overLiftIso]
  rw [Presieve.isSheafFor_iff_generate (R := Presieve.ofArrows Y f),
    Presieve.isSheafFor_iff_generate (R := Presieve.ofArrows (fun i ↦ overLift X (f i).left)
      (fun i ↦ overLiftι X (f i).left)), hgen]

/-- The Zariski sheaf condition on `Sch/S`, read at an arbitrary family of morphisms of `Sch/S`
whose underlying morphisms of schemes are open immersions whose ranges cover the target. -/
theorem IsZariskiCoverSheafOver.isSheafFor {G : (Over S)ᵒᵖ ⥤ Type w}
    (hZ : IsZariskiCoverSheafOver.{w, u, v} G) (X : Over S) {ι : Type v} (Y : ι → Over S)
    (f : ∀ i, Y i ⟶ X) (hoi : ∀ i, IsOpenImmersion (f i).left)
    (hcov : ∀ z : X.left, ∃ i, z ∈ Set.range (f i).left) :
    (Presieve.ofArrows Y f).IsSheafFor G :=
  (isSheafFor_ofArrows_iff_overLift Y f).mp
    (hZ X (Scheme.Cover.mkOfCovers ι (fun i ↦ (Y i).left) (fun i ↦ (f i).left)
      (fun z ↦ (hcov z).imp fun _ ↦ id) hoi))

/-! ### Generalities -/

/-- An object of `Sch/S` is isomorphic to the open subobject attached to the whole space of its
underlying scheme. -/
private noncomputable def overTopIso (T : Over S) : T ≅ overLift T (⊤ : T.left.Opens).ι :=
  Over.isoMk T.left.topIso.symm (by simp)

private lemma overTopIso_hom_comp (T : Over S) :
    (overTopIso T).hom ≫ overLiftι T (⊤ : T.left.Opens).ι = 𝟙 T := by
  apply Over.OverMorphism.ext
  show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι = 𝟙 T.left
  rw [← Scheme.topIso_hom]
  exact T.left.topIso.inv_hom_id

/-- The projections of the fibre product of the underlying schemes of two morphisms of `Sch/S`
with the same target are compatible with the structure morphisms. -/
private lemma pullback_fst_comp_hom {X V T : Over S} (f : X ⟶ T) (r : V ⟶ T) :
    pullback.fst f.left r.left ≫ X.hom = pullback.snd f.left r.left ≫ V.hom := by
  simp only [← Over.w f, ← Over.w r, pullback.condition_assoc]

/-- Two sections of a Zariski sheaf over an object are equal if they agree on the affine members
of the standard affine open cover of its underlying scheme. -/
private lemma eq_of_affineOpenCover {G : (Over S)ᵒᵖ ⥤ Type w}
    (hZ : IsZariskiCoverSheafOver.{w, u, max u v} G) (V : Over S) {a b : G.obj (op V)}
    (h : ∀ j, IsAffine (overLift V ((affineOpenCover.{u, v} V.left).f j)).left →
      G.map (overLiftι V ((affineOpenCover.{u, v} V.left).f j)).op a =
        G.map (overLiftι V ((affineOpenCover.{u, v} V.left).f j)).op b) :
    a = b :=
  eq_of_sheafFor_arrows _ (hZ V (affineOpenCover.{u, v} V.left)) fun j ↦
    h j (affineOpenNbhd_spec V.left j.down).1

/-- A standard V covering remains one after the index type is replaced by its `ULift`. -/
private lemma isStandardVCovering_ulift {T : Scheme.{u}} [IsAffine T] {I : Type*} [Finite I]
    {X : I → Scheme.{u}} [∀ i, IsAffine (X i)] {f : ∀ i, X i ⟶ T}
    (hf : IsStandardVCovering X f) :
    IsStandardVCovering (fun i : ULift.{max u v} I ↦ X i.down) (fun i ↦ f i.down) := by
  intro V _ _ _ g
  obtain ⟨W, hW₁, hW₂, hW₃, e, he, i, k, hk⟩ := hf V g
  exact ⟨W, hW₁, hW₂, hW₃, e, he, ULift.up i, k, hk⟩

/-! ### Local descent data -/

/-- The data produced over an affine open of the base object by the V covering hypothesis: a
finite standard V covering of that affine open refining the given family, together with the local
section it produces and the identity characterizing it. -/
private structure LocalDescentData {T : Over S} {I : Type v} {G : (Over S)ᵒᵖ ⥤ Type w}
    (X : I → Over S) (f : ∀ i, X i ⟶ T) (x : ∀ i, G.obj (op (X i)))
    (U : T.left.Opens) (hU : IsAffineOpen U) where
  /-- The refining family of schemes over the affine open. -/
  E : PreZeroHypercover.{max u v} U.toScheme
  /-- Its index type is finite. -/
  finite : Finite E.I₀
  /-- Its members are affine. -/
  affine : ∀ j, IsAffine (E.X j)
  /-- It is a standard V covering. -/
  standard : @AlgebraicGeometry.IsStandardVCovering U.toScheme hU E.I₀ finite E.X affine E.f
  /-- The member of the given family that each member of the refining family maps to. -/
  index : E.I₀ → I
  /-- The refinement morphism, as a morphism of `Sch/S`. -/
  toOriginal : ∀ j, overLift (overLift T U.ι) (E.f j) ⟶ X (index j)
  /-- The refinement morphism lies over the affine open. -/
  toOriginal_over : ∀ j, toOriginal j ≫ f (index j) =
    overLiftι (overLift T U.ι) (E.f j) ≫ overLiftι T U.ι
  /-- The section over the affine open. -/
  localSection : G.obj (op (overLift T U.ι))
  /-- It agrees with the given family on the refining covering. -/
  glue : ∀ j, G.map (overLiftι (overLift T U.ι) (E.f j)).op localSection =
    G.map (toOriginal j).op (x (index j))

/-- The local descent data exist over every affine open of the base object. -/
private lemma exists_localDescentData {T : Over S} {I : Type v} {G : (Over S)ᵒᵖ ⥤ Type w}
    (X : I → Over S) (f : ∀ i, X i ⟶ T) (x : ∀ i, G.obj (op (X i)))
    (hx : Presieve.Arrows.Compatible G f x)
    (hstd : IsStandardVSheafOver.{w, u, max u v} G)
    (hf : IsVCoveringOver f) (U : T.left.Opens) (hU : IsAffineOpen U) :
    Nonempty (LocalDescentData X f x U hU) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine (overLift T U.ι).left := hU
  obtain ⟨Es, hfinite, haffine, hstandard, hm⟩ := hf U hU
  have : Finite Es.I₀ := hfinite
  let ms := Classical.choice hm
  let E : PreZeroHypercover.{max u v} U.toScheme :=
    { I₀ := ULift.{max u v} Es.I₀
      X := fun j ↦ Es.X j.down
      f := fun j ↦ Es.f j.down }
  have : ∀ j, IsAffine (E.X j) := fun j ↦ haffine j.down
  have hEstd : @AlgebraicGeometry.IsStandardVCovering U.toScheme hU E.I₀ inferInstance E.X
      inferInstance E.f := by
    exact isStandardVCovering_ulift hstandard
  let idx : E.I₀ → I := fun j ↦ ms.s₀ j.down
  let h₀ : ∀ j : E.I₀, E.X j ⟶ pullback (f (idx j)).left U.ι := fun j ↦ ms.h₀ j.down
  have hsnd : ∀ j : E.I₀,
      h₀ j ≫ pullback.snd (f (idx j)).left U.ι = E.f j := fun j ↦ ms.w₀ j.down
  have : ∀ j, IsAffine (overLift (overLift T U.ι) (E.f j)).left := fun j ↦ haffine j.down
  have horigw : ∀ j : E.I₀,
      (h₀ j ≫ pullback.fst (f (idx j)).left U.ι) ≫ (X (idx j)).hom =
        E.f j ≫ U.ι ≫ T.hom := by
    intro j
    have hXi : (f (idx j)).left ≫ T.hom = (X (idx j)).hom := Over.w (f (idx j))
    simp only [← hXi, ← hsnd j, Category.assoc, pullback.condition_assoc]
  let orig : ∀ j, overLift (overLift T U.ι) (E.f j) ⟶ X (idx j) := fun j ↦
    Over.homMk (h₀ j ≫ pullback.fst (f (idx j)).left U.ι) (horigw j)
  have horig : ∀ j, orig j ≫ f (idx j) =
      overLiftι (overLift T U.ι) (E.f j) ≫ overLiftι T U.ι := by
    intro j
    apply Over.OverMorphism.ext
    show (h₀ j ≫ pullback.fst (f (idx j)).left U.ι) ≫ (f (idx j)).left = E.f j ≫ U.ι
    simp only [← hsnd j, Category.assoc, pullback.condition]
  let y : ∀ j, G.obj (op (overLift (overLift T U.ι) (E.f j))) := fun j ↦
    G.map (orig j).op (x (idx j))
  have hy : Presieve.Arrows.Compatible G
      (fun j ↦ overLiftι (overLift T U.ι) (E.f j)) y := by
    intro i j Z gi gj h
    have hbase : (gi ≫ orig i) ≫ f (idx i) = (gj ≫ orig j) ≫ f (idx j) := by
      simpa only [Category.assoc, horig] using congrArg (· ≫ overLiftι T U.ι) h
    dsimp only [y]
    rw [← types_comp_apply (G.map (orig i).op) (G.map gi.op), ← G.map_comp, ← op_comp,
      ← types_comp_apply (G.map (orig j).op) (G.map gj.op), ← G.map_comp, ← op_comp]
    exact hx (idx i) (idx j) Z (gi ≫ orig i) (gj ≫ orig j) hbase
  obtain ⟨s, hs, -⟩ := (Presieve.isSheafFor_arrows_iff G
    (fun j ↦ overLiftι (overLift T U.ι) (E.f j))).mp
      (hstd (overLift T U.ι) E.I₀ (fun j ↦ overLift (overLift T U.ι) (E.f j))
        (fun j ↦ overLiftι (overLift T U.ι) (E.f j)) hEstd) y hy
  exact ⟨⟨E, inferInstance, fun j ↦ haffine j.down, hEstd, idx, orig, horig, s, hs⟩⟩

/-! ### The local sections are determined -/

/-- The local section agrees with the given family on every morphism into a member of the refining
covering which, composed down to the base object, factors through a member of the family. -/
private lemma map_localSection_of_factor {T : Over S} {I : Type v} {G : (Over S)ᵒᵖ ⥤ Type w}
    {X : I → Over S} {f : ∀ i, X i ⟶ T} {x : ∀ i, G.obj (op (X i))}
    (hx : Presieve.Arrows.Compatible G f x) {U : T.left.Opens} {hU : IsAffineOpen U}
    (D : LocalDescentData X f x U hU) {W : Over S} (j : D.E.I₀)
    (p : W ⟶ overLift (overLift T U.ι) (D.E.f j)) (i : I) (q : W ⟶ X i)
    (hpq : p ≫ overLiftι (overLift T U.ι) (D.E.f j) ≫ overLiftι T U.ι = q ≫ f i) :
    G.map (p ≫ overLiftι (overLift T U.ι) (D.E.f j)).op D.localSection = G.map q.op (x i) := by
  have h := hx (D.index j) i W (p ≫ D.toOriginal j) q
    (by rw [Category.assoc, D.toOriginal_over j, hpq])
  rw [op_comp, G.map_comp, types_comp_apply] at h ⊢
  rwa [D.glue j]

/-- A section over the base object restricting to the given family restricts to the local
section over the affine open. -/
private lemma map_overLiftι_eq_localSection {T : Over S} {I : Type v}
    {G : (Over S)ᵒᵖ ⥤ Type w} {X : I → Over S} {f : ∀ i, X i ⟶ T} {x : ∀ i, G.obj (op (X i))}
    (hstd : IsStandardVSheafOver.{w, u, max u v} G) {U : T.left.Opens} {hU : IsAffineOpen U}
    (D : LocalDescentData X f x U hU) (t : G.obj (op T)) (ht : ∀ i, G.map (f i).op t = x i) :
    G.map (overLiftι T U.ι).op t = D.localSection := by
  have : IsAffine U.toScheme := hU
  have : IsAffine (overLift T U.ι).left := hU
  have : Finite D.E.I₀ := D.finite
  have : ∀ j, IsAffine (D.E.X j) := D.affine
  have : ∀ j, IsAffine (overLift (overLift T U.ι) (D.E.f j)).left := D.affine
  refine eq_of_sheafFor_arrows _ (hstd (overLift T U.ι) D.E.I₀
    (fun j ↦ overLift (overLift T U.ι) (D.E.f j))
    (fun j ↦ overLiftι (overLift T U.ι) (D.E.f j)) D.standard) fun j ↦ ?_
  have hleft : G.map (overLiftι (overLift T U.ι) (D.E.f j)).op (G.map (overLiftι T U.ι).op t) =
      G.map (D.toOriginal j).op (G.map (f (D.index j)).op t) := by
    simpa only [← types_comp_apply, ← G.map_comp, ← op_comp] using
      congrArg (fun m => G.map m.op t) (D.toOriginal_over j).symm
  rw [hleft, ht (D.index j), ← D.glue j]

/-- The local section is characterized by agreeing with the given family on every morphism from
an affine object into the affine open which factors through a member of the covering. -/
private lemma localSection_matchesOnAffine {T : Over S} {I : Type v} {G : (Over S)ᵒᵖ ⥤ Type w}
    {X : I → Over S} (f : ∀ i, X i ⟶ T) (x : ∀ i, G.obj (op (X i)))
    (hx : Presieve.Arrows.Compatible G f x)
    (hstd : IsStandardVSheafOver.{w, u, max u v} G)
    {U : T.left.Opens} (hU : IsAffineOpen U) (D : LocalDescentData X f x U hU)
    {V : Over S} (hV : IsAffine V.left) (g : V ⟶ overLift T U.ι)
    (i : I) (q : V ⟶ X i) (hq : g ≫ overLiftι T U.ι = q ≫ f i) :
    G.map g.op D.localSection = G.map q.op (x i) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.left := hV
  have : Finite D.E.I₀ := D.finite
  have : ∀ j, IsAffine (D.E.X j) := D.affine
  let Z : D.E.I₀ → Over S := fun j ↦ overLift V (pullback.snd (D.E.f j) g.left)
  let k : ∀ j, Z j ⟶ V := fun j ↦ overLiftι V (pullback.snd (D.E.f j) g.left)
  have : ∀ j, IsAffine (Z j).left := fun j ↦ by
    show IsAffine (pullback (D.E.f j) g.left)
    infer_instance
  have hs := hstd V D.E.I₀ Z k
    (AlgebraicGeometry.isStandardVCovering_pullback D.E.X D.E.f g.left D.standard)
  let y : ∀ j, G.obj (op (Z j)) := fun j ↦ G.map (k j).op (G.map g.op D.localSection)
  have hy : Presieve.Arrows.Compatible G k y := by
    intro j l W a b hab
    dsimp only [y]
    have hab' : a ≫ k j ≫ g = b ≫ k l ≫ g := by
      simpa only [Category.assoc] using congrArg (fun m => m ≫ g) hab
    simpa only [← types_comp_apply, ← G.map_comp, ← op_comp] using
      congrArg (fun m => G.map m.op D.localSection) hab'
  obtain ⟨t, ht, huniq⟩ := (Presieve.isSheafFor_arrows_iff G k).mp hs y hy
  let pf : ∀ j, Z j ⟶ overLift (overLift T U.ι) (D.E.f j) := fun j ↦
    Over.homMk (pullback.fst (D.E.f j) g.left)
      (pullback_fst_comp_hom (overLiftι (overLift T U.ι) (D.E.f j)) g)
  have hpf : ∀ j, k j ≫ g = pf j ≫ overLiftι (overLift T U.ι) (D.E.f j) := fun j ↦
    Over.OverMorphism.ext (pullback.condition (f := D.E.f j) (g := g.left)).symm
  have hright : ∀ j, G.map (k j).op (G.map q.op (x i)) = y j := by
    intro j
    have h := map_localSection_of_factor hx D j (pf j) i (k j ≫ q) (by
      rw [← Category.assoc, ← hpf j]
      simp only [Category.assoc, hq])
    rw [← hpf j] at h
    dsimp only [y]
    simpa only [← types_comp_apply, ← G.map_comp, ← op_comp] using h.symm
  exact (huniq _ fun _ ↦ rfl).trans (huniq _ hright).symm

/-! ### The sheaf condition over an affine object -/

/-- The sheaf condition for a V covering of an object of `Sch/S` with affine underlying scheme. -/
private lemma isSheafFor_vCovering_affine {T : Over S} (hT : IsAffine T.left)
    {I : Type (max u v)} {G : (Over S)ᵒᵖ ⥤ Type w} (X : I → Over S) (f : ∀ i, X i ⟶ T)
    (hf : IsVCoveringOver f)
    (hZ : IsZariskiCoverSheafOver.{w, u, max u v} G)
    (hstd : IsStandardVSheafOver.{w, u, max u v} G) :
    (Presieve.ofArrows X f).IsSheafFor G := by
  have : IsAffine T.left := hT
  have hU : IsAffineOpen (⊤ : T.left.Opens) := isAffineOpen_top T.left
  have : IsAffine (⊤ : T.left.Opens).toScheme := hU
  have : IsAffine (overLift T (⊤ : T.left.Opens).ι).left := hU
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  obtain ⟨D⟩ := exists_localDescentData X f x hx hstd hf (⊤ : T.left.Opens) hU
  let s : G.obj (op T) := G.map (overTopIso T).hom.op D.localSection
  have hmatch : ∀ i, G.map (f i).op s = x i := by
    intro i
    refine eq_of_affineOpenCover hZ (X i) fun j hVaff ↦ ?_
    have hg : (overLiftι (X i) ((affineOpenCover.{u, v} (X i).left).f j) ≫
          f i ≫ (overTopIso T).hom) ≫ overLiftι T (⊤ : T.left.Opens).ι =
        overLiftι (X i) ((affineOpenCover.{u, v} (X i).left).f j) ≫ f i := by
      simp only [Category.assoc, overTopIso_hom_comp, Category.comp_id]
    have hloc := localSection_matchesOnAffine f x hx hstd hU D hVaff
      (overLiftι (X i) ((affineOpenCover.{u, v} (X i).left).f j) ≫ f i ≫ (overTopIso T).hom) i
      (overLiftι (X i) ((affineOpenCover.{u, v} (X i).left).f j)) hg
    dsimp only [s]
    simpa only [← types_comp_apply, ← G.map_comp, ← op_comp, Category.assoc] using hloc
  refine ⟨s, hmatch, fun t ht ↦ ?_⟩
  simpa only [s, ← types_comp_apply, ← G.map_comp, ← op_comp, overTopIso_hom_comp, op_id,
    G.map_id, types_id_apply] using
    congrArg (fun z => G.map (overTopIso T).hom.op z) (map_overLiftι_eq_localSection hstd D t ht)

/-! ### The local sections are compatible -/

/-- The characterization of the local section, for a morphism out of an arbitrary object of
`Sch/S`. -/
private lemma localSection_matches {T : Over S} {I : Type v} {G : (Over S)ᵒᵖ ⥤ Type w}
    {X : I → Over S} (f : ∀ i, X i ⟶ T) (x : ∀ i, G.obj (op (X i)))
    (hx : Presieve.Arrows.Compatible G f x)
    (hZ : IsZariskiCoverSheafOver.{w, u, max u v} G)
    (hstd : IsStandardVSheafOver.{w, u, max u v} G)
    {U : T.left.Opens} (hU : IsAffineOpen U) (D : LocalDescentData X f x U hU)
    {V : Over S} (g : V ⟶ overLift T U.ι) (i : I) (q : V ⟶ X i)
    (hq : g ≫ overLiftι T U.ι = q ≫ f i) :
    G.map g.op D.localSection = G.map q.op (x i) := by
  refine eq_of_affineOpenCover hZ V fun j hVaff ↦ ?_
  have hqj : (overLiftι V ((affineOpenCover.{u, v} V.left).f j) ≫ g) ≫ overLiftι T U.ι =
      (overLiftι V ((affineOpenCover.{u, v} V.left).f j) ≫ q) ≫ f i := by
    simp only [Category.assoc, hq]
  have hloc := localSection_matchesOnAffine f x hx hstd hU D hVaff
    (overLiftι V ((affineOpenCover.{u, v} V.left).f j) ≫ g) i
    (overLiftι V ((affineOpenCover.{u, v} V.left).f j) ≫ q) hqj
  simpa only [← types_comp_apply, ← G.map_comp, ← op_comp] using hloc

/-- Two local sections agree on an affine object mapping into both affine opens. -/
private lemma localSections_compatible_affine {T : Over S} {I : Type (max u v)}
    {G : (Over S)ᵒᵖ ⥤ Type w} {X : I → Over S} (f : ∀ i, X i ⟶ T)
    (x : ∀ i, G.obj (op (X i))) (hx : Presieve.Arrows.Compatible G f x)
    (hf : IsVCoveringOver f)
    (hZ : IsZariskiCoverSheafOver.{w, u, max u v} G)
    (hstd : IsStandardVSheafOver.{w, u, max u v} G)
    {U₁ U₂ : T.left.Opens} (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (D₁ : LocalDescentData X f x U₁ hU₁) (D₂ : LocalDescentData X f x U₂ hU₂)
    {V : Over S} (hV : IsAffine V.left) (g₁ : V ⟶ overLift T U₁.ι)
    (g₂ : V ⟶ overLift T U₂.ι)
    (hbase : g₁ ≫ overLiftι T U₁.ι = g₂ ≫ overLiftι T U₂.ι) :
    G.map g₁.op D₁.localSection = G.map g₂.op D₂.localSection := by
  let r : V ⟶ T := g₁ ≫ overLiftι T U₁.ι
  let Y : I → Over S := fun i ↦ overLift V (pullback.snd (f i).left r.left)
  let p : ∀ i, Y i ⟶ V := fun i ↦ overLiftι V (pullback.snd (f i).left r.left)
  let q : ∀ i, Y i ⟶ X i := fun i ↦
    Over.homMk (pullback.fst (f i).left r.left) (pullback_fst_comp_hom (f i) r)
  have hqp : ∀ i, p i ≫ r = q i ≫ f i := fun i ↦
    Over.OverMorphism.ext (pullback.condition (f := (f i).left) (g := r.left)).symm
  let y : ∀ i, G.obj (op (Y i)) := fun i ↦ G.map (q i).op (x i)
  have hfV : IsVCoveringOver p :=
    AlgebraicGeometry.isVCovering_pullback (fun i ↦ (X i).left) (fun i ↦ (f i).left) r.left hf
  have hsheaf := isSheafFor_vCovering_affine hV Y p hfV hZ hstd
  have hleft : ∀ i, G.map (p i).op (G.map g₁.op D₁.localSection) = y i := by
    intro i
    have heq : (p i ≫ g₁) ≫ overLiftι T U₁.ι = q i ≫ f i := by
      simpa only [Category.assoc] using hqp i
    have hloc₁ := localSection_matches f x hx hZ hstd hU₁ D₁ (p i ≫ g₁) i (q i) heq
    simpa only [← types_comp_apply, ← G.map_comp, ← op_comp] using hloc₁
  have hright : ∀ i, G.map (p i).op (G.map g₂.op D₂.localSection) = y i := by
    intro i
    have heq : (p i ≫ g₂) ≫ overLiftι T U₂.ι = q i ≫ f i := by
      rw [Category.assoc, ← hbase]
      simpa only [Category.assoc] using hqp i
    have hloc₂ := localSection_matches f x hx hZ hstd hU₂ D₂ (p i ≫ g₂) i (q i) heq
    simpa only [← types_comp_apply, ← G.map_comp, ← op_comp] using hloc₂
  exact eq_of_sheafFor_arrows p hsheaf fun i ↦ (hleft i).trans (hright i).symm

/-- Two local sections agree on any object of `Sch/S` mapping into both affine opens. -/
private lemma localSections_compatible {T : Over S} {I : Type (max u v)}
    {G : (Over S)ᵒᵖ ⥤ Type w} {X : I → Over S} (f : ∀ i, X i ⟶ T)
    (x : ∀ i, G.obj (op (X i))) (hx : Presieve.Arrows.Compatible G f x)
    (hf : IsVCoveringOver f)
    (hZ : IsZariskiCoverSheafOver.{w, u, max u v} G)
    (hstd : IsStandardVSheafOver.{w, u, max u v} G)
    {U₁ U₂ : T.left.Opens} (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (D₁ : LocalDescentData X f x U₁ hU₁) (D₂ : LocalDescentData X f x U₂ hU₂)
    {Z : Over S} (g₁ : Z ⟶ overLift T U₁.ι) (g₂ : Z ⟶ overLift T U₂.ι)
    (hbase : g₁ ≫ overLiftι T U₁.ι = g₂ ≫ overLiftι T U₂.ι) :
    G.map g₁.op D₁.localSection = G.map g₂.op D₂.localSection := by
  refine eq_of_affineOpenCover hZ Z fun j hVaff ↦ ?_
  have hbase' : (overLiftι Z ((affineOpenCover.{u, v} Z.left).f j) ≫ g₁) ≫ overLiftι T U₁.ι =
      (overLiftι Z ((affineOpenCover.{u, v} Z.left).f j) ≫ g₂) ≫ overLiftι T U₂.ι := by
    simp only [Category.assoc, hbase]
  have hlocal := localSections_compatible_affine f x hx hf hZ hstd hU₁ hU₂ D₁ D₂ hVaff
    (overLiftι Z ((affineOpenCover.{u, v} Z.left).f j) ≫ g₁)
    (overLiftι Z ((affineOpenCover.{u, v} Z.left).f j) ≫ g₂) hbase'
  simpa only [← types_comp_apply, ← G.map_comp, ← op_comp] using hlocal

/-! ### The reduction -/

/-- A functor on `Sch/S` which is a sheaf for the Zariski coverings and satisfies the sheaf
condition for the standard V coverings of the affine objects is a sheaf for the V topology. -/
theorem isVSheafOver_of_zariski_of_standard {G : (Over S)ᵒᵖ ⥤ Type w}
    (hZ : IsZariskiCoverSheafOver.{w, u, max u v} G)
    (hstd : IsStandardVSheafOver.{w, u, max u v} G) : IsVSheafOver.{w, u, max u v} G := by
  intro I T X f hf
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  let 𝒰 := affineOpenCover.{u, v} T.left
  let U : 𝒰.I₀ → T.left.Opens := fun a ↦ affineOpenNbhd T.left a.down
  have hU : ∀ a, IsAffineOpen (U a) := fun a ↦ (affineOpenNbhd_spec T.left a.down).1
  let D : ∀ a, LocalDescentData X f x (U a) (hU a) := fun a ↦
    Classical.choice (exists_localDescentData X f x hx hstd hf (U a) (hU a))
  let y : ∀ a, G.obj (op (overLift T (U a).ι)) := fun a ↦ (D a).localSection
  have hy : Presieve.Arrows.Compatible G (fun a ↦ overLiftι T (U a).ι) y :=
    fun a b _ g₁ g₂ hab ↦ localSections_compatible f x hx hf hZ hstd (hU a) (hU b) (D a) (D b)
      g₁ g₂ hab
  obtain ⟨s, hs, -⟩ := (Presieve.isSheafFor_arrows_iff G
    (fun a ↦ overLiftι T (U a).ι)).mp (hZ T 𝒰) y hy
  have hmatch : ∀ i, G.map (f i).op s = x i := by
    intro i
    let 𝒱 := 𝒰.pullback₁ (f i).left
    refine eq_of_sheafFor_arrows (fun a ↦ overLiftι (X i) (𝒱.f a))
      (hZ (X i) 𝒱) fun a ↦ ?_
    let g : overLift (X i) (𝒱.f a) ⟶ overLift T (U a).ι :=
      Over.homMk (pullback.snd (f i).left (𝒰.f a))
        (pullback_fst_comp_hom (f i) (overLiftι T (U a).ι)).symm
    have hq : g ≫ overLiftι T (U a).ι = overLiftι (X i) (𝒱.f a) ≫ f i :=
      Over.OverMorphism.ext (pullback.condition (f := (f i).left) (g := 𝒰.f a)).symm
    calc G.map (overLiftι (X i) (𝒱.f a)).op (G.map (f i).op s)
        = G.map (overLiftι (X i) (𝒱.f a) ≫ f i).op s := by
          rw [← types_comp_apply, ← G.map_comp, ← op_comp]
      _ = G.map (g ≫ overLiftι T (U a).ι).op s := by rw [hq]
      _ = G.map g.op (G.map (overLiftι T (U a).ι).op s) := by
          rw [← types_comp_apply, ← G.map_comp, ← op_comp]
      _ = G.map g.op (D a).localSection := congrArg _ (hs a)
      _ = G.map (overLiftι (X i) (𝒱.f a)).op (x i) :=
          localSection_matches f x hx hZ hstd (hU a) (D a) g i _ hq
  exact ⟨s, hmatch, fun t ht ↦ eq_of_sheafFor_arrows _ (hZ T 𝒰) fun a ↦
    (map_overLiftι_eq_localSection hstd (D a) t ht).trans (hs a).symm⟩

/-- **The relative form of Stacks 0ETM.** A functor on `Sch/S` is a sheaf for the V topology if
and only if it is a sheaf for the Zariski coverings of `Sch/S` and satisfies the sheaf condition
for the families whose underlying family of schemes is a standard V covering of an affine
scheme. -/
@[sga "3 XI 3.4" "special case"]
theorem isVSheafOver_iff_zariski_and_standard (G : (Over S)ᵒᵖ ⥤ Type w) :
    IsVSheafOver.{w, u, max u v} G ↔
      IsZariskiCoverSheafOver.{w, u, max u v} G ∧ IsStandardVSheafOver.{w, u, max u v} G := by
  constructor
  · intro hV
    refine ⟨?_, ?_⟩
    · intro T 𝒰
      exact hV T _ _ (isVCoveringOver_openCover 𝒰)
    · intro T _ ι _ Y _ f hf
      exact hV T Y f (standardCovering_isVCovering (X := fun i ↦ (Y i).left)
        (f := fun i ↦ (f i).left) hf)
  · rintro ⟨hZ, hstd⟩
    exact isVSheafOver_of_zariski_of_standard hZ hstd

/-! ### The coproducts of `Sch/S` -/

/-- The coproduct of a family of objects of `Sch/S`, built from the coproduct of the underlying
schemes. -/
private noncomputable def overSigma {ι : Type*} (X : ι → Over S) [Small.{u} ι] : Over S :=
  Over.mk (Sigma.desc (fun i ↦ (X i).hom))

/-- The injection of a member of a family of objects of `Sch/S` into their coproduct. -/
private noncomputable def overSigmaι {ι : Type*} (X : ι → Over S) [Small.{u} ι] (i : ι) :
    X i ⟶ overSigma X :=
  Over.homMk (Sigma.ι (fun i ↦ (X i).left) i)
    (by change Sigma.ι (fun i ↦ (X i).left) i ≫ Sigma.desc (fun i ↦ (X i).hom) = (X i).hom
        exact Sigma.ι_desc _ i)

/-- The coproduct cofan of a family of objects of `Sch/S`. -/
private noncomputable def overCofan {ι : Type*} (X : ι → Over S) [Small.{u} ι] : Cofan X :=
  Cofan.mk (overSigma X) (overSigmaι X)

/-- The coproduct cofan of a family of objects of `Sch/S` is a colimit: a coproduct of `Sch/S` is
the coproduct of the underlying schemes, with the induced structure morphism. This is
`AlgebraicGeometry.isColimitCofanOfIsColimitLeft` at the cofan of the underlying schemes. -/
private noncomputable def isColimitOverCofan {ι : Type*} (X : ι → Over S) [Small.{u} ι] :
    IsColimit (overCofan X) :=
  isColimitCofanOfIsColimitLeft (overCofan X) (coproductIsCoproduct fun i ↦ (X i).left)

/-- The coproduct cofans of `Sch/S` are van Kampen: `Over.forget S` creates colimits and
preserves pullbacks, and the finite coproducts of `Scheme` are van Kampen. -/
private theorem isVanKampenColimit_of_isColimit {ι : Type*} [Finite ι] {X : ι → Over S}
    {c : Cocone (Discrete.functor X)} (hc : IsColimit c) : IsVanKampenColimit c :=
  IsVanKampenColimit.of_mapCocone (Over.forget S)
    (FinitaryExtensive.isVanKampen_finiteCoproducts (isColimitOfPreserves (Over.forget S) hc))

/-- The initial object of `Sch/S`: the empty scheme over `S`. -/
private noncomputable def overInitial (S : Scheme.{u}) : Over S := Over.mk (initial.to S)

/-- The empty scheme over `S` is an initial object of `Sch/S`. -/
private noncomputable def isInitial_overInitial : IsInitial (overInitial S) :=
  IsInitial.ofUniqueHom (fun Y ↦ Over.homMk (initial.to Y.left) (initial.hom_ext _ _))
    fun _ _ ↦ Over.OverMorphism.ext (initial.hom_ext _ _)

/-- A Zariski sheaf on `Sch/S` preserves the products of a finite family of objects: the
coproducts of `Sch/S` are disjoint and are covered by their summands, which is the Zariski
condition read at those coverings. -/
private lemma preservesDiscreteOfZariski {G : (Over S)ᵒᵖ ⥤ Type w}
    (hZ : IsZariskiCoverSheafOver.{w, u, max u v} G)
    {I : Type (max u v)} [Finite I] (X : I → Over S) :
    PreservesLimit (Discrete.functor (fun i ↦ op (X i))) G := by
  have hIE : IsEmpty ↥(overInitial S).left := by
    show IsEmpty ↥(⊥_ Scheme.{u})
    infer_instance
  let 𝒰₀ : (overInitial S).left.OpenCover.{max u v} :=
    Scheme.Cover.mkOfCovers (ULift.{max u v} Empty) (fun i ↦ i.down.elim)
      (fun i ↦ i.down.elim) (fun z ↦ hIE.elim z) (fun i ↦ i.down.elim)
  have hEmpty : (Presieve.ofArrows (X := overInitial S) Empty.elim
      Empty.instIsEmpty.elim).IsSheafFor G := by
    have h₁ : Presieve.ofArrows (fun i ↦ overLift (overInitial S) (𝒰₀.f i))
        (fun i ↦ overLiftι (overInitial S) (𝒰₀.f i)) = (⊥ : Presieve (overInitial S)) :=
      le_antisymm (Presieve.ofArrows_le_iff.2 fun i ↦ i.down.elim) bot_le
    have h₂ : Presieve.ofArrows (X := overInitial S) Empty.elim Empty.instIsEmpty.elim =
        (⊥ : Presieve (overInitial S)) :=
      le_antisymm (Presieve.ofArrows_le_iff.2 fun i ↦ i.elim) bot_le
    rw [h₂, ← h₁]
    exact hZ (overInitial S) 𝒰₀
  have hoi : ∀ i, IsOpenImmersion (Sigma.ι (fun i ↦ (X i).left) i) := fun i ↦
    (AlgebraicGeometry.sigmaOpenCover (fun i ↦ (X i).left)).map_prop i
  have hsurj : ∀ z : ↥(∐ fun i ↦ (X i).left),
      ∃ i, z ∈ Set.range (Sigma.ι (fun i ↦ (X i).left) i) := fun z ↦
    (AlgebraicGeometry.sigmaOpenCover (fun i ↦ (X i).left)).exists_eq z
  have hc : IsColimit (overCofan X) := isColimitOverCofan X
  have hvk : IsVanKampenColimit (overCofan X) := isVanKampenColimit_of_isColimit hc
  have hd : Pairwise fun i j ↦ IsPullback (initial.to _) (initial.to _)
      ((overCofan X).inj i) ((overCofan X).inj j) := fun i j hij ↦
    isPullback_initial_to_of_cofan_isVanKampen hvk ⟨i⟩ ⟨j⟩ fun h ↦ hij (congrArg Discrete.as h)
  have : ∀ i, Mono ((overCofan X).inj i) := fun i ↦ mono_of_cofan_isVanKampen hvk ⟨i⟩
  have hcover : (Presieve.ofArrows X (overCofan X).inj).IsSheafFor G :=
    hZ.isSheafFor (overSigma X) X (overSigmaι X) hoi hsurj
  exact Presieve.preservesProduct_of_isSheafFor _ hEmpty isInitial_overInitial
    (overCofan X) hc hd hcover

/-- **The relative form of the last assertion of Stacks 0ETM.** Under the Zariski sheaf condition
on `Sch/S`, the sheaf condition for the families whose underlying family is a standard V covering
of an affine scheme may be tested on the families of a single arrow. -/
theorem isStandardVSheafOver_iff_singleton (G : (Over S)ᵒᵖ ⥤ Type w)
    (hZ : IsZariskiCoverSheafOver.{w, u, max u v} G) :
    IsStandardVSheafOver.{w, u, max u v} G ↔
      ∀ (T Y : Over S) [IsAffine T.left] [IsAffine Y.left] (f : Y ⟶ T),
        IsStandardVCovering (fun _ : Unit ↦ Y.left) (fun _ ↦ f.left) →
          (Presieve.ofArrows (fun _ : Unit ↦ Y) (fun _ ↦ f)).IsSheafFor G := by
  refine Iff.intro ?mp ?mpr
  case mp =>
    intro h T Y _ _ f hf
    have hs := h T (ULift.{max u v} Unit) (fun _ ↦ Y) (fun _ ↦ f) (isStandardVCovering_ulift hf)
    rwa [constOfArrows_eq f (I := ULift.{max u v} Unit) (J := Unit)] at hs
  case mpr =>
    intro h T _ I _ Y _ f hf
    have := preservesDiscreteOfZariski hZ Y
    have := preservesDiscreteOfZariski hZ (fun ij : I × I ↦ Limits.pullback (f ij.1) (f ij.2))
    let hc : IsColimit (overCofan Y) := isColimitOverCofan Y
    have hcu : IsUniversalColimit (overCofan Y) :=
      (isVanKampenColimit_of_isColimit hc).isUniversal
    have : IsAffine (overCofan Y).pt.left := by
      show IsAffine (∐ fun i ↦ (Y i).left)
      infer_instance
    have hdleft : (Cofan.IsColimit.desc hc f).left = Sigma.desc (fun i ↦ (f i).left) := by
      refine Sigma.hom_ext _ _ fun i ↦ ?_
      rw [Sigma.ι_desc]
      exact (Over.forget S).congr_map (Cofan.IsColimit.fac hc f i)
    have hstdSigma : IsStandardVCovering (fun _ : Unit ↦ (overCofan Y).pt.left)
        (fun _ ↦ (Cofan.IsColimit.desc hc f).left) := by
      rw [hdleft]
      exact ((AlgebraicGeometry.isStandardVCovering_tfae
        (fun i ↦ (Y i).left) (fun i ↦ (f i).left)).out 1 3).mp hf
    have hsingle := h T (overCofan Y).pt (Cofan.IsColimit.desc hc f) hstdSigma
    have heq : Presieve.ofArrows (fun _ : Unit ↦ (overCofan Y).pt)
        (fun _ ↦ Cofan.IsColimit.desc hc f) =
        Presieve.singleton (Cofan.IsColimit.desc hc f) :=
      le_antisymm (Presieve.ofArrows_le_iff.2 fun _ ↦ Presieve.singleton_self _)
        ((Presieve.singleton_le_iff _).2 ⟨()⟩)
    rw [heq] at hsingle
    exact (Presieve.isSheafFor_sigmaDesc_iff f hc hcu G).mp hsingle

end AlgebraicGeometry.ExtendingFunctors
