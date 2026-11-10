module

public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatStratificationLength
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.MorphismFlatStratificationQcqs
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.FlatteningApproximation
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.FlatteningSurjective
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafCartesian
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafReduction
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafThickening
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.EqualizerTransport

/-!
# The sufficiency direction of the almost blowup criterion

Stacks 0EVF characterizes the sheaves on the big h site over a scheme `S` by three conditions on
a presheaf of sets `F`:

1. `F` is a sheaf for the Zariski topology;
2. for every morphism `f : X ⟶ Y` of the site with `Y` affine and `f` surjective, flat, proper
   and of finite presentation, `F(Y)` is the equalizer of the two maps `F(X) ⟶ F(X ×_Y X)`;
3. for every almost blowup square of the site whose base is affine, `F` of the square is
   cartesian in sets.

This file proves the sufficiency direction: the three conditions force condition (2′) of
Stacks 0EU5, the sheaf condition for every morphism of the site with affine target which is
proper, surjective and of finite presentation, and hence the sheaf condition. Combined with the
necessity direction,
`AlgebraicGeometry.BigHOver.zariski_and_affineFlatProperFP_and_affineAlmostBlowUp_of_isSheaf`,
this gives the characterization of Stacks 0EVF.

## Main definitions

* `AlgebraicGeometry.BigHOver.objOver`: the object of the big h category over `S` given by a
  scheme of the site mapping to the underlying scheme of an object.
* `AlgebraicGeometry.BigHOver.objOverHom`: its structure morphism to that object.

## Main results

* `AlgebraicGeometry.BigHOver.isSheafFor_singleton_of_isFlatStratification`: the sheaf condition
  for a morphism of the site with affine target which is proper, surjective and of finite
  presentation and which carries a flat stratification of its target with a prescribed number of
  strata.
* `AlgebraicGeometry.BigHOver.isAffineProperFinitePresentationSheaf_of_conditions`: condition
  (2′) of Stacks 0EU5.
* `AlgebraicGeometry.BigHOver.isSheaf_of_zariski_and_affineFlatProperFP_and_affineAlmostBlowUp`:
  the three conditions force the sheaf condition.
* `AlgebraicGeometry.BigHOver.isSheaf_iff_zariski_and_affineFlatProperFP_and_affineAlmostBlowUp`:
  the characterization, Stacks 0EVF.

## References

* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
* [Stacks Project, Tag 0EVC](https://stacks.math.columbia.edu/tag/0EVC)
* [Stacks Project, Tag 0EV8](https://stacks.math.columbia.edu/tag/0EV8)
* [Stacks Project, Tag 0EU5](https://stacks.math.columbia.edu/tag/0EU5)
* [Stacks Project, Tag 0H3Z](https://stacks.math.columbia.edu/tag/0H3Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w₁ w₂ w₃

namespace AlgebraicGeometry

/-! ### A diagram chase for presheaves of sets -/

/-- Let `G` be a presheaf of sets on a category and consider a diagram

```
Eo --------> Do
|  \       /  |
|   Yp <- Xp  |
|   |     |   |
|   Yo <- Xo  |
Zo --------> To
```

satisfying the five commutativities `hfz`, `hfb`, `hdge`, `hdgp` and `hqc`, whose two side
squares `G` sends to cartesian squares of sets. If `G` satisfies the sheaf condition for `{fT}` and
for `{g}`, and is separated for `{dg}`, then it satisfies the sheaf condition for `{f}`. -/
private theorem isSheafFor_singleton_of_isPullback_of_isSheafFor
    {C : Type w₁} [Category.{w₂} C] (G : Cᵒᵖ ⥤ Type w₃)
    {Yo Xo Yp Xp Zo To Eo Do : C} (f : Xo ⟶ Yo) (b : Yp ⟶ Yo) (c : Xp ⟶ Xo) (g : Xp ⟶ Yp)
    (z : Zo ⟶ Yo) (tx : To ⟶ Xo) (fT : To ⟶ Zo) (p : Eo ⟶ Yp) (e : Eo ⟶ Zo) (q : Do ⟶ Xp)
    (dt : Do ⟶ To) (dg : Do ⟶ Eo)
    (hfz : tx ≫ f = fT ≫ z) (hfb : c ≫ f = g ≫ b) (hdge : dg ≫ e = dt ≫ fT)
    (hdgp : dg ≫ p = q ≫ g) (hqc : q ≫ c = dt ≫ tx)
    (hY : IsPullback (G.map z.op) (G.map b.op) (G.map e.op) (G.map p.op))
    (hX : IsPullback (G.map tx.op) (G.map c.op) (G.map dt.op) (G.map q.op))
    (hg : Presieve.IsSheafFor G (Presieve.singleton g))
    (hd : Presieve.IsSeparatedFor G (Presieve.singleton dg))
    (hfT : Presieve.IsSheafFor G (Presieve.singleton fT)) :
    Presieve.IsSheafFor G (Presieve.singleton f) := by
  have key : ∀ {A A' A'' : C} (α : A ⟶ A') (β : A' ⟶ A'') (s : G.obj (op A'')),
      G.map α.op (G.map β.op s) = G.map (α ≫ β).op s := by
    intro A A' A'' α β s
    rw [← Functor.map_comp_apply, ← op_comp]
  have hinj : Function.Injective (G.map dg.op) := by
    intro a a' haa
    refine hd.ext ?_
    rintro W m ⟨⟩
    exact haa
  rw [Presieve.isSheafFor_singleton] at hg hfT ⊢
  intro x hx
  obtain ⟨tz, htz, htzu⟩ := hfT (G.map tx.op x) (by
    intro W q₁ q₂ hq
    rw [key, key]
    refine hx (q₁ ≫ tx) (q₂ ≫ tx) ?_
    rw [Category.assoc, Category.assoc, hfz, ← Category.assoc, ← Category.assoc, hq])
  obtain ⟨ty, hty, htyu⟩ := hg (G.map c.op x) (by
    intro W q₁ q₂ hq
    rw [key, key]
    refine hx (q₁ ≫ c) (q₂ ≫ c) ?_
    rw [Category.assoc, Category.assoc, hfb, ← Category.assoc, ← Category.assoc, hq])
  have hagree : G.map e.op tz = G.map p.op ty := by
    refine hinj ?_
    rw [key, key, hdge, hdgp, ← key, htz, ← key, hty, key, key, hqc]
  obtain ⟨u, hu₁, hu₂⟩ := Types.exists_of_isPullback hY tz ty hagree
  refine ⟨u, Types.ext_of_isPullback hX ?_ ?_, ?_⟩
  · rw [key, hfz, ← key, hu₁, htz]
  · rw [key, hfb, ← key, hu₂, hty]
  · intro u' hu'
    have h₁ : G.map z.op u' = tz := htzu _ (by beta_reduce; rw [key, ← hfz, ← key, hu'])
    have h₂ : G.map b.op u' = ty := htyu _ (by beta_reduce; rw [key, ← hfb, ← key, hu'])
    exact Types.ext_of_isPullback hY (by rw [h₁, hu₁]) (by rw [h₂, hu₂])

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)

/-- An object of the big h category over `S` from a scheme of the site mapping to the
underlying scheme of an object. -/
public def objOver {X : BigHOver B S hS} {T : Scheme.{u}} (hT : B.Contains T)
    (b : T ⟶ (BigHOver.toScheme B S hS).obj X) : BigHOver B S hS :=
  Over.mk ((ObjectProperty.homMk b :
    (B.obj T hT) ⟶ (BigHOver.forget B S hS).obj X) ≫ X.hom)

/-- The structure morphism of `AlgebraicGeometry.BigHOver.objOver` to the object it lies over. -/
public def objOverHom {X : BigHOver B S hS} {T : Scheme.{u}} (hT : B.Contains T)
    (b : T ⟶ (BigHOver.toScheme B S hS).obj X) : objOver B S hS hT b ⟶ X :=
  Over.homMk (ObjectProperty.homMk b) (by simp [objOver])

/-- The underlying scheme of `AlgebraicGeometry.BigHOver.objOver` is the given scheme. -/
@[simp]
public theorem toScheme_obj_objOver {X : BigHOver B S hS} {T : Scheme.{u}} (hT : B.Contains T)
    (b : T ⟶ (BigHOver.toScheme B S hS).obj X) :
    (BigHOver.toScheme B S hS).obj (objOver B S hS hT b) = T := rfl

/-- The underlying morphism of `AlgebraicGeometry.BigHOver.objOverHom` is the given morphism. -/
@[simp]
public theorem toScheme_map_objOverHom {X : BigHOver B S hS} {T : Scheme.{u}} (hT : B.Contains T)
    (b : T ⟶ (BigHOver.toScheme B S hS).obj X) :
    (BigHOver.toScheme B S hS).map (objOverHom B S hS hT b) = b := rfl

/-- The underlying morphism of schemes to `S` of an object of the big h category over `S`. -/
private abbrev structureMap (A : BigHOver B S hS) :
    (BigHOver.toScheme B S hS).obj A ⟶ S :=
  B.inclusion.map A.hom

/-- A morphism of the big h category over `S` built from a morphism of the underlying schemes
commuting with the structure morphisms to `S`. -/
private def homMk {A A' : BigHOver B S hS}
    (m : (BigHOver.toScheme B S hS).obj A ⟶ (BigHOver.toScheme B S hS).obj A')
    (hm : m ≫ structureMap B S hS A' = structureMap B S hS A) : A ⟶ A' :=
  Over.homMk (ObjectProperty.homMk m) (B.inclusion.map_injective (by
    rw [Functor.map_comp]
    exact hm))

/-- The underlying morphism of schemes of `AlgebraicGeometry.BigHOver.homMk` is the given
morphism of schemes. -/
@[simp]
private theorem toScheme_map_homMk {A A' : BigHOver B S hS}
    (m : (BigHOver.toScheme B S hS).obj A ⟶ (BigHOver.toScheme B S hS).obj A')
    (hm : m ≫ structureMap B S hS A' = structureMap B S hS A) :
    (BigHOver.toScheme B S hS).map (homMk B S hS m hm) = m := rfl

/-- Two morphisms of the big h category over `S` with the same underlying morphism of schemes
are equal, the inclusion of the site into schemes being faithful. -/
private theorem hom_ext_toScheme {A A' : BigHOver B S hS} {α β : A ⟶ A'}
    (h : (BigHOver.toScheme B S hS).map α = (BigHOver.toScheme B S hS).map β) : α = β :=
  Over.OverMorphism.ext (B.inclusion.map_injective h)

/-- The structure morphism to `S` of `AlgebraicGeometry.BigHOver.objOver` is the given morphism
followed by the structure morphism of the object it lies over. -/
@[simp]
private theorem structureMap_objOver {A : BigHOver B S hS} {T : Scheme.{u}} (hT : B.Contains T)
    (b : T ⟶ (BigHOver.toScheme B S hS).obj A) :
    structureMap B S hS (objOver B S hS hT b) = b ≫ structureMap B S hS A :=
  B.inclusion.map_comp _ _

/-- A morphism of the big h category over `S` commutes with the structure morphisms to `S`. -/
@[simp]
private theorem toScheme_map_comp_structureMap {A A' : BigHOver B S hS} (m : A ⟶ A') :
    (BigHOver.toScheme B S hS).map m ≫ structureMap B S hS A' = structureMap B S hS A :=
  calc (BigHOver.toScheme B S hS).map m ≫ structureMap B S hS A'
      = B.inclusion.map ((BigHOver.forget B S hS).map m ≫ A'.hom) :=
        (B.inclusion.map_comp _ _).symm
    _ = structureMap B S hS A := congrArg _ (Over.w m)

/-- A morphism between two objects of the big h category over `S` of the form
`AlgebraicGeometry.BigHOver.objOver` over one and the same object, from a morphism of the given
schemes commuting with the two given morphisms to the underlying scheme of that object. -/
private def objOverMap {A : BigHOver B S hS} {T T' : Scheme.{u}} (hT : B.Contains T)
    (hT' : B.Contains T') {β : T ⟶ (BigHOver.toScheme B S hS).obj A}
    {β' : T' ⟶ (BigHOver.toScheme B S hS).obj A} (m : T ⟶ T') (hm : m ≫ β' = β) :
    objOver B S hS hT β ⟶ objOver B S hS hT' β' :=
  homMk B S hS m (by
    change m ≫ β' ≫ structureMap B S hS A = β ≫ structureMap B S hS A
    rw [← hm, Category.assoc])

/-- The underlying morphism of schemes of `AlgebraicGeometry.BigHOver.objOverMap` is the given
morphism of schemes. -/
@[simp]
private theorem toScheme_map_objOverMap {A : BigHOver B S hS} {T T' : Scheme.{u}}
    (hT : B.Contains T) (hT' : B.Contains T')
    {β : T ⟶ (BigHOver.toScheme B S hS).obj A} {β' : T' ⟶ (BigHOver.toScheme B S hS).obj A}
    (m : T ⟶ T') (hm : m ≫ β' = β) :
    (BigHOver.toScheme B S hS).map (objOverMap B S hS hT hT' m hm) = m := rfl

/-- A morphism between two objects of the big h category over `S` of the form
`AlgebraicGeometry.BigHOver.objOver` lying over two different objects of the site, from a
morphism of the given schemes commuting with the two given morphisms through a morphism of the
site. -/
private def objOverMapOver {A A' : BigHOver B S hS} (a : A ⟶ A') {T T' : Scheme.{u}}
    (hT : B.Contains T) (hT' : B.Contains T')
    {β : T ⟶ (BigHOver.toScheme B S hS).obj A} {β' : T' ⟶ (BigHOver.toScheme B S hS).obj A'}
    (m : T ⟶ T') (hm : m ≫ β' = β ≫ (BigHOver.toScheme B S hS).map a) :
    objOver B S hS hT β ⟶ objOver B S hS hT' β' :=
  homMk B S hS m (by
    change m ≫ β' ≫ structureMap B S hS A' = β ≫ structureMap B S hS A
    rw [← toScheme_map_comp_structureMap B S hS a, ← Category.assoc, hm, Category.assoc])

/-- The underlying morphism of schemes of `AlgebraicGeometry.BigHOver.objOverMapOver` is the
given morphism of schemes. -/
@[simp]
private theorem toScheme_map_objOverMapOver {A A' : BigHOver B S hS} (a : A ⟶ A')
    {T T' : Scheme.{u}} (hT : B.Contains T) (hT' : B.Contains T')
    {β : T ⟶ (BigHOver.toScheme B S hS).obj A} {β' : T' ⟶ (BigHOver.toScheme B S hS).obj A'}
    (m : T ⟶ T') (hm : m ≫ β' = β ≫ (BigHOver.toScheme B S hS).map a) :
    (BigHOver.toScheme B S hS).map (objOverMapOver B S hS a hT hT' m hm) = m := rfl

/-- **The induction step of the sufficiency direction of Stacks 0EVF.** Let `f : X ⟶ Y` be a
morphism of the big h category over `S` with affine target which is proper, surjective and of
finite presentation, and let `V` be a quasi-compact open of the underlying scheme of `Y` over
which `f` is flat.  Assume that for every centre on `Y` disjoint from `V` the base change of `f`
to the closed subscheme it cuts out carries a flat stratification with `t + 1` members — and
assume the sheaf condition for every morphism of the site with affine target carrying such a
stratification.  Then `F` satisfies the sheaf condition for `{f}`. -/
private theorem isSheafFor_singleton_of_isCompact_of_flat
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (h2 : BigHOver.IsAffineFlatProperFinitePresentationSheaf B S hS F)
    (h3 : BigHOver.IsAffineAlmostBlowUpSheaf B S hS F) {t : ℕ}
    (IH : ∀ (X Y : BigHOver B S hS) (f : X ⟶ Y),
      IsAffine ((BigHOver.toScheme B S hS).obj Y) →
      IsProper ((BigHOver.toScheme B S hS).map f) →
      Surjective ((BigHOver.toScheme B S hS).map f) →
      FinitePresentation ((BigHOver.toScheme B S hS).map f) →
      ∀ I : Fin (t + 1) → ((BigHOver.toScheme B S hS).obj Y).IdealSheafData,
        IsFlatStratification ((BigHOver.toScheme B S hS).map f) t I →
        Presieve.IsSheafFor F (Presieve.singleton f))
    {X Y : BigHOver B S hS} (f : X ⟶ Y)
    (haff : IsAffine ((BigHOver.toScheme B S hS).obj Y))
    (hproper : IsProper ((BigHOver.toScheme B S hS).map f))
    (hsurj : Surjective ((BigHOver.toScheme B S hS).map f))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map f))
    (V : ((BigHOver.toScheme B S hS).obj Y).Opens)
    (hVqc : IsCompact (V : Set ((BigHOver.toScheme B S hS).obj Y)))
    (hVflat : Flat (pullback.snd ((BigHOver.toScheme B S hS).map f) V.ι))
    (hstrat : ∀ Zc : ((BigHOver.toScheme B S hS).obj Y).IdealSheafData,
      Disjoint (V : Set ((BigHOver.toScheme B S hS).obj Y))
        (Zc.support : Set ((BigHOver.toScheme B S hS).obj Y)) →
      ∃ J : Fin (t + 1) → Zc.subscheme.IdealSheafData,
        IsFlatStratification
          (pullback.snd ((BigHOver.toScheme B S hS).map f) Zc.subschemeι) t J) :
    Presieve.IsSheafFor F (Presieve.singleton f) := by
  have : IsAffine ((BigHOver.toScheme B S hS).obj Y) := haff
  have : IsProper ((BigHOver.toScheme B S hS).map f) := hproper
  have : Surjective ((BigHOver.toScheme B S hS).map f) := hsurj
  have : LocallyOfFinitePresentation ((BigHOver.toScheme B S hS).map f) := hfp.1
  have : QuasiCompact ((BigHOver.toScheme B S hS).map f) := hfp.2.1
  have : QuasiSeparated ((BigHOver.toScheme B S hS).map f) := hfp.2.2
  obtain ⟨Zc, Y', b, X', c, g, hbsq, hcsq, hdisj, hgb, hgflat, hgfp, hgproper, hgsurj⟩ :=
    exists_surjective_of_hasFlatAlmostBlowUpSquarePair ((BigHOver.toScheme B S hS).map f)
      hproper hsurj V
      (hasFlatAlmostBlowUpSquarePair_of_flat ((BigHOver.toScheme B S hS).map f) hfp V hVqc hVflat)
  have : IsProper b := hbsq.proper
  have : LocallyOfFinitePresentation b := hbsq.finitePresentation.1
  have : QuasiCompact b := hbsq.finitePresentation.2.1
  have : IsProper c := hcsq.proper
  have : LocallyOfFinitePresentation c := hcsq.finitePresentation.1
  have : QuasiCompact c := hcsq.finitePresentation.2.1
  have : Flat g := hgflat
  have : IsProper g := hgproper
  have : Surjective g := hgsurj
  have : LocallyOfFinitePresentation g := hgfp.1
  have : QuasiCompact g := hgfp.2.1
  have : QuasiSeparated g := hgfp.2.2
  have hZcaff : IsAffine Zc.subscheme := isAffine_of_isAffineHom Zc.subschemeι
  have hYsize : ((BigHOver.toScheme B S hS).obj Y).size < B.cutoff :=
    ((BigHOver.forget B S hS).obj Y).2
  have hXsize : ((BigHOver.toScheme B S hS).obj X).size < B.cutoff :=
    ((BigHOver.forget B S hS).obj X).2
  have hY'size : Y'.size < B.cutoff :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact b hYsize
  have hX'size : X'.size < B.cutoff :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact c hXsize
  have hZsize : Zc.subscheme.size < B.cutoff :=
    Scheme.size_lt_of_isClosedImmersion Zc.subschemeι hYsize
  have hTsize :
      (pullback ((BigHOver.toScheme B S hS).map f) Zc.subschemeι).size < B.cutoff :=
    Scheme.size_pullback_lt _ _ hXsize hZsize
  have hEsize : (pullback Zc.subschemeι b).size < B.cutoff :=
    Scheme.size_pullback_lt _ _ hZsize hY'size
  have hDsize : (pullback g (pullback.snd Zc.subschemeι b)).size < B.cutoff :=
    Scheme.size_pullback_lt _ _ hX'size hEsize
  have hTsq : IsPullback (pullback.fst ((BigHOver.toScheme B S hS).map f) Zc.subschemeι)
      (pullback.snd ((BigHOver.toScheme B S hS).map f) Zc.subschemeι)
      ((BigHOver.toScheme B S hS).map f) Zc.subschemeι := IsPullback.of_hasPullback _ _
  have hEsq : IsPullback (pullback.fst Zc.subschemeι b) (pullback.snd Zc.subschemeι b)
      Zc.subschemeι b := IsPullback.of_hasPullback _ _
  have hDsq : IsPullback (pullback.snd g (pullback.snd Zc.subschemeι b))
      (pullback.fst g (pullback.snd Zc.subschemeι b)) (pullback.snd Zc.subschemeι b) g :=
    (IsPullback.of_hasPullback _ _).flip
  have hpaste : IsPullback
      (pullback.snd g (pullback.snd Zc.subschemeι b) ≫ pullback.fst Zc.subschemeι b)
      (pullback.fst g (pullback.snd Zc.subschemeι b)) Zc.subschemeι
      (c ≫ (BigHOver.toScheme B S hS).map f) := by
    rw [← hgb]
    exact hDsq.paste_horiz hEsq
  obtain ⟨dt, hdtfT, hdttx, hXsq⟩ :
      ∃ dt : pullback g (pullback.snd Zc.subschemeι b) ⟶
          pullback ((BigHOver.toScheme B S hS).map f) Zc.subschemeι,
        dt ≫ pullback.snd ((BigHOver.toScheme B S hS).map f) Zc.subschemeι =
            pullback.snd g (pullback.snd Zc.subschemeι b) ≫ pullback.fst Zc.subschemeι b ∧
          dt ≫ pullback.fst ((BigHOver.toScheme B S hS).map f) Zc.subschemeι =
            pullback.fst g (pullback.snd Zc.subschemeι b) ≫ c ∧
            IsPullback dt (pullback.fst g (pullback.snd Zc.subschemeι b))
              (pullback.fst ((BigHOver.toScheme B S hS).map f) Zc.subschemeι) c :=
    ⟨_, hTsq.flip.lift_fst _ _ _, hTsq.flip.lift_snd _ _ _,
      IsPullback.of_right' hpaste hTsq.flip⟩
  let Yp : BigHOver B S hS := objOver B S hS hY'size b
  let Zo : BigHOver B S hS := objOver B S hS hZsize Zc.subschemeι
  let Eo : BigHOver B S hS := objOver B S hS hEsize (pullback.snd Zc.subschemeι b ≫ b)
  let Xp : BigHOver B S hS := objOver B S hS hX'size c
  let To : BigHOver B S hS :=
    objOver B S hS hTsize (pullback.fst ((BigHOver.toScheme B S hS).map f) Zc.subschemeι)
  let Do : BigHOver B S hS :=
    objOver B S hS hDsize (pullback.fst g (pullback.snd Zc.subschemeι b) ≫ c)
  let bo : Yp ⟶ Y := objOverHom B S hS hY'size b
  let zo : Zo ⟶ Y := objOverHom B S hS hZsize Zc.subschemeι
  let co : Xp ⟶ X := objOverHom B S hS hX'size c
  let txo : To ⟶ X :=
    objOverHom B S hS hTsize (pullback.fst ((BigHOver.toScheme B S hS).map f) Zc.subschemeι)
  let po : Eo ⟶ Yp :=
    objOverMap B S hS hEsize hY'size (pullback.snd Zc.subschemeι b) rfl
  let eo : Eo ⟶ Zo :=
    objOverMap B S hS hEsize hZsize (pullback.fst Zc.subschemeι b) hEsq.w
  let qo : Do ⟶ Xp :=
    objOverMap B S hS hDsize hX'size (pullback.fst g (pullback.snd Zc.subschemeι b)) rfl
  let dto : Do ⟶ To := objOverMap B S hS hDsize hTsize dt hdttx
  let go : Xp ⟶ Yp := objOverMapOver B S hS f hX'size hY'size g hgb
  let fTo : To ⟶ Zo :=
    objOverMapOver B S hS f hTsize hZsize
      (pullback.snd ((BigHOver.toScheme B S hS).map f) Zc.subschemeι) hTsq.w.symm
  let dgo : Do ⟶ Eo :=
    objOverMapOver B S hS f hDsize hEsize (pullback.snd g (pullback.snd Zc.subschemeι b))
      (by rw [← Category.assoc, hDsq.w, Category.assoc, hgb, Category.assoc])
  obtain ⟨J, hJ⟩ := hstrat Zc hdisj
  refine isSheafFor_singleton_of_isPullback_of_isSheafFor F f bo co go zo txo fTo po eo qo dto
    dgo ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hom_ext_toScheme B S hS (by
      rw [Functor.map_comp, Functor.map_comp]; exact hTsq.w)
  · exact hom_ext_toScheme B S hS (by
      rw [Functor.map_comp, Functor.map_comp]; exact hgb.symm)
  · exact hom_ext_toScheme B S hS (by
      rw [Functor.map_comp, Functor.map_comp]; exact hdtfT.symm)
  · exact hom_ext_toScheme B S hS (by
      rw [Functor.map_comp, Functor.map_comp]; exact hDsq.w)
  · exact hom_ext_toScheme B S hS (by
      rw [Functor.map_comp, Functor.map_comp]; exact hdttx.symm)
  · exact isPullback_of_isAffineAlmostBlowUpSheaf B S hS F hZ h3 Y Yp Zo Eo bo zo po eo Zc
      hbsq ⟨Iso.refl _⟩ hEsq
  · exact isPullback_of_isAffineAlmostBlowUpSheaf B S hS F hZ h3 X Xp To Do co txo qo dto
      (Zc.comap ((BigHOver.toScheme B S hS).map f)) hcsq
      ⟨Over.isoMk (Zc.comapIso ((BigHOver.toScheme B S hS).map f)).symm
        (Zc.comapIso_inv_subschemeι ((BigHOver.toScheme B S hS).map f))⟩ hXsq
  · exact isSheafFor_singleton_of_flat B S hS F hZ h2 go hgflat hgproper hgsurj hgfp
  · exact (isSheafFor_singleton_of_flat B S hS F hZ h2 dgo
      (inferInstance : Flat (pullback.snd g (pullback.snd Zc.subschemeι b)))
      (inferInstance : IsProper (pullback.snd g (pullback.snd Zc.subschemeι b)))
      (inferInstance : Surjective (pullback.snd g (pullback.snd Zc.subschemeι b)))
      (⟨inferInstance, inferInstance, inferInstance⟩ :
        FinitePresentation (pullback.snd g (pullback.snd Zc.subschemeι b)))).isSeparatedFor
  · exact IH To Zo fTo hZcaff
      (inferInstance :
        IsProper (pullback.snd ((BigHOver.toScheme B S hS).map f) Zc.subschemeι))
      (inferInstance :
        Surjective (pullback.snd ((BigHOver.toScheme B S hS).map f) Zc.subschemeι))
      (⟨inferInstance, inferInstance, inferInstance⟩ :
        FinitePresentation (pullback.snd ((BigHOver.toScheme B S hS).map f) Zc.subschemeι))
      J hJ

/-- **Conditions (1), (2) and (3) of Stacks 0EVF force condition (2′) of Stacks 0EU5 for a
morphism carrying a flat stratification with a prescribed number of strata.** Let `F` be a
presheaf of sets on the big h category over `S` which is a sheaf for Zariski coverings, which
satisfies the sheaf condition for every morphism of the site with affine target that is flat,
proper, surjective and of finite presentation, and which sends every almost blowup square of the
site with affine base to a cartesian square of sets.  Then `F` satisfies the sheaf condition for
the one-element family `{f}` attached to every morphism `f : X ⟶ Y` of the site with affine
target which is proper, surjective and of finite presentation and whose target carries a flat
stratification with `t` strata for `f`. -/
public theorem isSheafFor_singleton_of_isFlatStratification
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (h2 : BigHOver.IsAffineFlatProperFinitePresentationSheaf B S hS F)
    (h3 : BigHOver.IsAffineAlmostBlowUpSheaf B S hS F) (t : ℕ) :
    ∀ (X Y : BigHOver B S hS) (f : X ⟶ Y),
      IsAffine ((BigHOver.toScheme B S hS).obj Y) →
      IsProper ((BigHOver.toScheme B S hS).map f) →
      Surjective ((BigHOver.toScheme B S hS).map f) →
      FinitePresentation ((BigHOver.toScheme B S hS).map f) →
      ∀ I : Fin (t + 1) → ((BigHOver.toScheme B S hS).obj Y).IdealSheafData,
        IsFlatStratification ((BigHOver.toScheme B S hS).map f) t I →
        Presieve.IsSheafFor F (Presieve.singleton f) := by
  induction t with
  | zero =>
    intro X Y f _ _ _ _ I hI
    have hYempty : IsEmpty ((BigHOver.toScheme B S hS).obj Y) := hI.isEmpty
    have hXempty : IsEmpty ((BigHOver.toScheme B S hS).obj X) :=
      Function.isEmpty fun x ↦ ((BigHOver.toScheme B S hS).map f) x
    obtain ⟨hXsub, -⟩ := BigHOver.subsingleton_of_isEmpty B S hS F hZ X hXempty
    obtain ⟨hYsub, hYne⟩ := BigHOver.subsingleton_of_isEmpty B S hS F hZ Y hYempty
    rw [Presieve.isSheafFor_singleton]
    exact fun x _ ↦ ⟨hYne.some, hXsub.elim _ _, fun y _ ↦ hYsub.elim _ _⟩
  | succ t IH =>
    intro X Y f haff hproper hsurj hfp I hI
    have : IsAffine ((BigHOver.toScheme B S hS).obj Y) := haff
    have : IsProper ((BigHOver.toScheme B S hS).map f) := hproper
    have : Surjective ((BigHOver.toScheme B S hS).map f) := hsurj
    have : LocallyOfFinitePresentation ((BigHOver.toScheme B S hS).map f) := hfp.1
    have : QuasiCompact ((BigHOver.toScheme B S hS).map f) := hfp.2.1
    have : QuasiSeparated ((BigHOver.toScheme B S hS).map f) := hfp.2.2
    have ⟨hthick, hft, _, _, hflat⟩ := hI
    have hKfp : FinitePresentation (I 0).subschemeι :=
      (finitePresentation_subschemeι_iff_isFiniteType (I 0)).mpr (hft 0)
    have hYsize : ((BigHOver.toScheme B S hS).obj Y).size < B.cutoff :=
      ((BigHOver.forget B S hS).obj Y).2
    have hXsize : ((BigHOver.toScheme B S hS).obj X).size < B.cutoff :=
      ((BigHOver.forget B S hS).obj X).2
    have hKsize : (I 0).subscheme.size < B.cutoff :=
      Scheme.size_lt_of_isClosedImmersion (I 0).subschemeι hYsize
    have hPsize :
        (pullback ((BigHOver.toScheme B S hS).map f) (I 0).subschemeι).size < B.cutoff :=
      Scheme.size_pullback_lt _ _ hXsize hKsize
    have hKaff : IsAffine (I 0).subscheme := isAffine_of_isAffineHom (I 0).subschemeι
    have hbcproper :
        IsProper (pullback.snd ((BigHOver.toScheme B S hS).map f) (I 0).subschemeι) :=
      inferInstance
    have hbcsurj :
        Surjective (pullback.snd ((BigHOver.toScheme B S hS).map f) (I 0).subschemeι) :=
      inferInstance
    have hbcfp :
        FinitePresentation
          (pullback.snd ((BigHOver.toScheme B S hS).map f) (I 0).subschemeι) :=
      ⟨inferInstance, inferInstance, inferInstance⟩
    refine isSheafFor_singleton_of_isSheafFor_singleton_of_isThickening B S hS F hZ h3 f
      (objOverMapOver B S hS f hPsize hKsize
        (pullback.snd ((BigHOver.toScheme B S hS).map f) (I 0).subschemeι)
        pullback.condition.symm)
      (objOverHom B S hS hKsize (I 0).subschemeι)
      (objOverHom B S hS hPsize
        (pullback.fst ((BigHOver.toScheme B S hS).map f) (I 0).subschemeι))
      (IsPullback.of_hasPullback _ _) hthick hKfp ?_
    rcases t with _ | t'
    · exact h2 _ _ _ hKaff hI.flat_of_eq_one hbcproper hbcsurj hbcfp
    · have hflat0 := hflat 0
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at hflat0
      refine isSheafFor_singleton_of_isCompact_of_flat B S hS F hZ h2 h3 IH _ hKaff hbcproper
        hbcsurj hbcfp ((I 0).subschemeι ⁻¹ᵁ (I 1).support.compl) hI.isCompact_stratum
        (MorphismProperty.pullbackSnd_of_comm (P := @Flat)
          ((BigHOver.toScheme B S hS).map f) _ (I 0).subschemeι (𝟙 _) _
          (Category.id_comp _) hflat0) ?_
      intro Zc hdisj
      have hbot : (I 0).comap (I 0).subschemeι = ⊥ := by
        change (pullback.fst (I 0).subschemeι (I 0).subschemeι).ker = ⊥
        exact Scheme.Hom.ker_eq_bot_of_isIso _
      have hcomapK : IsFlatStratification
          (pullback.snd ((BigHOver.toScheme B S hS).map f) (I 0).subschemeι) (t' + 2)
          (fun k ↦ (I k).comap (I 0).subschemeι) :=
        hI.comap (I 0) (by simp [hbot, Scheme.IdealSheafData.support_bot])
      refine ⟨_, (hcomapK.comap Zc
        (by simp [hbot, Scheme.IdealSheafData.support_bot])).succ ?_⟩
      rw [Set.eq_univ_iff_forall]
      intro w
      have hw : Zc.subschemeι w ∈ (Zc.support : Set _) := by
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact Set.mem_range_self w
      have hnot := Set.disjoint_right.mp hdisj hw
      simp only [Scheme.IdealSheafData.support_comap,
        TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage] at hnot ⊢
      by_contra hcon
      exact hnot hcon

/-- **Conditions (1), (2) and (3) of Stacks 0EVF force condition (2′) of Stacks 0EU5.** A
presheaf of sets on the big h category over `S` which is a sheaf for Zariski coverings, which
satisfies the sheaf condition for every morphism of the site with affine target that is flat,
proper, surjective and of finite presentation, and which sends every almost blowup square of the
site with affine base to a cartesian square of sets, satisfies the sheaf condition for *every*
morphism of the site with affine target which is proper, surjective and of finite presentation —
flatness is no longer required. -/
public theorem isAffineProperFinitePresentationSheaf_of_conditions
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (h2 : BigHOver.IsAffineFlatProperFinitePresentationSheaf B S hS F)
    (h3 : BigHOver.IsAffineAlmostBlowUpSheaf B S hS F) :
    BigHOver.IsAffineProperFinitePresentationSheaf B S hS F := by
  intro Yo Xo f haff hproper hsurj hfp
  have : IsAffine ((BigHOver.toScheme B S hS).obj Yo) := haff
  have : QuasiCompact ((BigHOver.toScheme B S hS).map f) := hfp.2.1
  have : QuasiSeparated ((BigHOver.toScheme B S hS).map f) := hfp.2.2
  have : CompactSpace ((BigHOver.toScheme B S hS).obj Xo) :=
    QuasiCompact.compactSpace_of_compactSpace ((BigHOver.toScheme B S hS).map f)
  have : QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj Xo) :=
    quasiSeparatedSpace_of_quasiSeparated ((BigHOver.toScheme B S hS).map f)
  obtain ⟨t, I, hI⟩ :=
    (hasFlatStratification_iff ((BigHOver.toScheme B S hS).map f)).mp
      (HasFlatStratification.of_finitePresentation ((BigHOver.toScheme B S hS).map f) hfp)
  exact isSheafFor_singleton_of_isFlatStratification B S hS F hZ h2 h3 t Xo Yo f haff hproper
    hsurj hfp I hI

/-! ### The three conditions force the sheaf condition -/

/-- **Stacks 0EVF, the three conditions are sufficient.** A presheaf of sets on the big h
category over `S` which satisfies condition (1), the sheaf condition for Zariski coverings,
condition (2), the sheaf condition for every morphism of the site with affine target which is
flat, proper, surjective and of finite presentation, and condition (3), the cartesianness of the
image of every almost blowup square of the site with affine base, is a sheaf for the h topology. -/
@[stacks 0EVF]
public theorem isSheaf_of_zariski_and_affineFlatProperFP_and_affineAlmostBlowUp
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (h2 : BigHOver.IsAffineFlatProperFinitePresentationSheaf B S hS F)
    (h3 : BigHOver.IsAffineAlmostBlowUpSheaf B S hS F) :
    Presheaf.IsSheaf (BigHOver.topology B S hS) F :=
  (isSheaf_iff_isSheaf_of_type _ _).2
    (isSheaf_of_isZariskiSheaf_of_isProperFinitePresentationSheaf hZ
      (isProperFinitePresentationSheaf_of_affine hZ
        (isAffineProperFinitePresentationSheaf_of_conditions B S hS F hZ h2 h3)))

/-- **Stacks 0EVF.** A presheaf of sets on the big h category over `S` is a sheaf for the h
topology if and only if it satisfies condition (1), the sheaf condition for Zariski coverings,
condition (2), the sheaf condition for every morphism of the site with affine target which is
flat, proper, surjective and of finite presentation, and condition (3), the cartesianness of the
image of every almost blowup square of the site with affine base. -/
@[stacks 0EVF]
public theorem isSheaf_iff_zariski_and_affineFlatProperFP_and_affineAlmostBlowUp :
    Presheaf.IsSheaf (BigHOver.topology B S hS) F ↔
      (BigHOver.IsZariskiSheaf B S hS F ∧
        BigHOver.IsAffineFlatProperFinitePresentationSheaf B S hS F ∧
        BigHOver.IsAffineAlmostBlowUpSheaf B S hS F) :=
  ⟨zariski_and_affineFlatProperFP_and_affineAlmostBlowUp_of_isSheaf B S hS F,
    fun ⟨hZ, h2, h3⟩ ↦
      isSheaf_of_zariski_and_affineFlatProperFP_and_affineAlmostBlowUp B S hS F hZ h2 h3⟩

end BigHOver

end AlgebraicGeometry

end
