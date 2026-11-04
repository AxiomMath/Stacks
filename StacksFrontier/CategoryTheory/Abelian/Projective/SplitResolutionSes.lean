module

public import StacksFrontier.CategoryTheory.Abelian.Projective.DerivedTransfer
public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe

/-! # Lifting a horseshoe into a split short exact sequence of arbitrary resolutions

`StacksFrontier/CategoryTheory/Abelian/Projective/Horseshoe.lean` lifts a morphism of short exact
sequences to a morphism of *horseshoes*, commuting on the nose
(`CategoryTheory.ShortComplex.Horseshoe.mapSesHom`), which is what the naturality of the
connecting morphism of the left derived functors consumes.

Reading that construction line by line shows that the projectivity of its **target** is used in
exactly two places: the lift of `φ.τ₁` and the uncorrected lift of `φ.τ₂`, both
`CategoryTheory.ProjectiveResolution.lift`. Everything else — the homotopy correcting the middle
lift, the induced map on the third resolutions, and all four commutation squares — uses only the
splitting and the epimorphy of the **source** horseshoe, and the homotopy already goes through
the generalized `CategoryTheory.ProjectiveResolution.liftHomotopy'`. Substituting
`CategoryTheory.ProjectiveResolution.lift'` in those two places therefore weakens the hypothesis
on the target to: a degreewise split short exact sequence of *arbitrary* resolutions of the three
terms, with no projectivity.

That is the situation which arises whenever a left derived functor on one abelian category is
compared with a left derived functor on another: the image of a horseshoe under an exact functor
is a degreewise split short exact sequence of resolutions, and it is never a sequence of
projective resolutions.

## Main definitions

* `CategoryTheory.ShortComplex.SplitResolutionSes`: a degreewise split short exact sequence of
  resolutions of the three terms of a short complex.
* `CategoryTheory.ShortComplex.Horseshoe.toSplitResolutionSes`: a horseshoe is one.
* `CategoryTheory.ShortComplex.SplitResolutionSes.mapExact`: the image of one under an exact
  additive functor, as one for the image short complex.
* `CategoryTheory.ShortComplex.SplitResolutionSes.mapSesHom`: a morphism of short complexes lifts
  to a morphism from a horseshoe sequence to such a sequence, on the nose.

## Main results

* `CategoryTheory.ShortComplex.SplitResolutionSes.ses_shortExact` and `mapSes_shortExact`: the
  sequence, and its image under an additive functor, are short exact.
* `CategoryTheory.ShortComplex.SplitResolutionSes.δ_naturality`: the connecting morphisms of the
  two mapped sequences are intertwined by `mapSesHom`.

## Implementation notes

**`_root_.QuasiIso`.** Inside the namespace `CategoryTheory.ShortComplex` the identifier
`QuasiIso` resolves to `ShortComplex.QuasiIso`, which takes a morphism of short complexes; the
error surfaces as an application type mismatch on the augmentation field. The three quasi-
isomorphism fields are therefore written `_root_.QuasiIso`.

They are instance-implicit fields and are made instances, as
`Stacks.CategoryHomology.HomologicalDeltaFunctor.Coeffacement.epi` is: the discrimination-tree
key of e.g. `quasiIsoA` is headed by the projection `SplitResolutionSes.εA`, so the instance is
not even considered for a goal `QuasiIso ε` with `ε` anything else.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
* Weibel, *An introduction to homological algebra*, Lemma 2.2.8.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Preadditive

universe v u v₂ u₂

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A **degreewise split short exact sequence of resolutions** of the three terms of a short
complex `S`: three chain complexes with augmentations which are quasi-isomorphisms, assembled
into a short complex of complexes which is split in every degree and whose two maps cover `S.f`
and `S.g` on the augmentations.

This is `CategoryTheory.ShortComplex.Horseshoe` with the projectivity of the three complexes
dropped. It is what the image of a horseshoe under an exact functor is. -/
structure SplitResolutionSes (S : ShortComplex C) where
  /-- a resolution of `S.X₁` -/
  KA : ChainComplex C ℕ
  /-- a resolution of `S.X₂` -/
  KB : ChainComplex C ℕ
  /-- a resolution of `S.X₃` -/
  KC : ChainComplex C ℕ
  /-- the augmentation of `KA` -/
  εA : KA ⟶ (ChainComplex.single₀ C).obj S.X₁
  /-- the augmentation of `KB` -/
  εB : KB ⟶ (ChainComplex.single₀ C).obj S.X₂
  /-- the augmentation of `KC` -/
  εC : KC ⟶ (ChainComplex.single₀ C).obj S.X₃
  [quasiIsoA : _root_.QuasiIso εA]
  [quasiIsoB : _root_.QuasiIso εB]
  [quasiIsoC : _root_.QuasiIso εC]
  /-- the chain map covering `S.f` -/
  ι : KA ⟶ KB
  /-- the chain map covering `S.g` -/
  p : KB ⟶ KC
  /-- the two chain maps compose to zero -/
  w : ι ≫ p = 0
  /-- the sequence of complexes is split in every degree -/
  splitting : ∀ n, (ShortComplex.mk (ι.f n) (p.f n)
    (by rw [← HomologicalComplex.comp_f, w, HomologicalComplex.zero_f])).Splitting
  /-- `ι` covers `S.f` -/
  commι : ι ≫ εB = εA ≫ (ChainComplex.single₀ C).map S.f
  /-- `p` covers `S.g` -/
  commp : p ≫ εC = εB ≫ (ChainComplex.single₀ C).map S.g

/-- The connecting morphism of a horseshoe, at the spelling
`CategoryTheory.ProjectiveResolution.isoLeftDerivedObj` rather than `Horseshoe.isoPA` and
`Horseshoe.isoPC`. -/
lemma Horseshoe.δ_eq {S : ShortComplex C} (H : Horseshoe S) [HasProjectiveResolutions C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) [F.Additive] (n : ℕ) :
    H.δ F n = (H.PC.isoLeftDerivedObj F (n + 1)).hom ≫
      (H.mapSes_shortExact F).δ (n + 1) n (down_rel_succ n) ≫
        (H.PA.isoLeftDerivedObj F n).inv :=
  rfl

namespace SplitResolutionSes

attribute [instance] quasiIsoA quasiIsoB quasiIsoC

section Sequence

variable {S : ShortComplex C} (R : SplitResolutionSes S)

/-- The short complex of chain complexes carried by a split sequence of resolutions. -/
def ses : ShortComplex (ChainComplex C ℕ) := ShortComplex.mk R.ι R.p R.w

/-- It is short exact, being split in every degree. -/
lemma ses_shortExact : R.ses.ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    fun n => (R.splitting n).shortExact

/-- The two maps compose to zero in each degree. -/
lemma ι_comp_p_f (n : ℕ) : R.ι.f n ≫ R.p.f n = 0 := by
  rw [← HomologicalComplex.comp_f, R.w, HomologicalComplex.zero_f]

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- The image of the sequence under an additive functor. -/
def mapSes (F : C ⥤ D) [F.Additive] : ShortComplex (ChainComplex D ℕ) :=
  R.ses.map (F.mapHomologicalComplex (ComplexShape.down ℕ))

/-- An additive functor preserves the degreewise splitting, hence the short exactness. -/
lemma mapSes_shortExact (F : C ⥤ D) [F.Additive] : (R.mapSes F).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    fun n => ((R.splitting n).map F).shortExact

/-- **The image of a split sequence of resolutions under an exact additive functor**, as a split
sequence of resolutions of the image short complex. The augmentations stay quasi-isomorphisms
because an exact functor preserves homology; this is the construction for whose sake the
projectivity hypothesis was dropped. -/
def mapExact (W : C ⥤ D) [W.Additive] [W.PreservesHomology] : SplitResolutionSes (S.map W) where
  KA := (W.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.KA
  KB := (W.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.KB
  KC := (W.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.KC
  εA := W.mapAugmentation R.εA
  εB := W.mapAugmentation R.εB
  εC := W.mapAugmentation R.εC
  ι := (W.mapHomologicalComplex (ComplexShape.down ℕ)).map R.ι
  p := (W.mapHomologicalComplex (ComplexShape.down ℕ)).map R.p
  w := by rw [← Functor.map_comp, R.w, Functor.map_zero]
  splitting := fun n => (R.splitting n).map W
  commι := by
    rw [Functor.map_comp_mapAugmentation, R.commι, Functor.mapAugmentation_comp_single₀_map]
    rfl
  commp := by
    rw [Functor.map_comp_mapAugmentation, R.commp, Functor.mapAugmentation_comp_single₀_map]
    rfl

/-- The image under an exact additive functor of the short complex of complexes carried by a
split sequence of resolutions. -/
lemma mapExact_ses (W : C ⥤ D) [W.Additive] [W.PreservesHomology] :
    (R.mapExact W).ses = R.mapSes W :=
  rfl

end Sequence

/-- A null-homotopic chain map into an augmented complex vanishes on the augmentation. This is
`CategoryTheory.ShortComplex.nullHomotopicMap_comp_π` with the target no longer required to be a
projective resolution: only `Q.d 1 0 ≫ ε.f 0 = 0` is used. -/
lemma nullHomotopicMap_comp_aug {P Q : ChainComplex C ℕ} {Z : C}
    (ε : Q ⟶ (ChainComplex.single₀ C).obj Z) (k : ∀ i j, P.X i ⟶ Q.X j) :
    Homotopy.nullHomotopicMap k ≫ ε = 0 :=
  to_single₀_eq _ _ (by
    rw [HomologicalComplex.comp_f, ChainComplex.nullHomotopicMap_f_zero,
      HomologicalComplex.zero_f, Category.assoc, ChainComplex.d_one_zero_comp_f_zero, comp_zero])

section Lift

variable {S T : ShortComplex C} (H : Horseshoe S) (R : SplitResolutionSes T) (φ : S ⟶ T)

/-- The lift of `φ.τ₁` from the first resolution of the horseshoe to the first resolution of the
target, by `CategoryTheory.ProjectiveResolution.lift'`. -/
def mapτ₁ : H.PA.complex ⟶ R.KA := ProjectiveResolution.lift' φ.τ₁ H.PA R.εA

/-- `mapτ₁` covers `φ.τ₁`. -/
lemma mapτ₁_comm : mapτ₁ H R φ ≫ R.εA = H.PA.π ≫ (ChainComplex.single₀ C).map φ.τ₁ :=
  ProjectiveResolution.lift'_commutes _ _ _

/-- An uncorrected lift of `φ.τ₂` to the middle resolutions. Its square against the inclusions
commutes only up to homotopy, which `mapτ₂` corrects. -/
def mapτ₂Aux : H.PB.complex ⟶ R.KB := ProjectiveResolution.lift' φ.τ₂ H.PB R.εB

/-- `mapτ₂Aux` covers `φ.τ₂`. -/
lemma mapτ₂Aux_comm : mapτ₂Aux H R φ ≫ R.εB = H.PB.π ≫ (ChainComplex.single₀ C).map φ.τ₂ :=
  ProjectiveResolution.lift'_commutes _ _ _

/-- The homotopy measuring the failure of the square against the inclusions to commute. It
exists because both composites cover `S.f ≫ φ.τ₂ = φ.τ₁ ≫ T.f`. -/
def ιHomotopy : _root_.Homotopy (H.ι ≫ mapτ₂Aux H R φ) (mapτ₁ H R φ ≫ R.ι) :=
  ProjectiveResolution.liftHomotopy' R.εB _ _ (by
    simp only [Category.assoc]
    rw [mapτ₂Aux_comm, reassoc_of% H.commι, ← Functor.map_comp, R.commι,
      reassoc_of% mapτ₁_comm, ← Functor.map_comp, φ.comm₁₂])

/-- The corrected lift of `φ.τ₂`: subtract from `mapτ₂Aux` the null-homotopic map built from
`ιHomotopy` pushed along the retraction of the splitting of `H`. Because the retraction splits
`H.ι`, the correction restricts along `H.ι` to exactly the defect, so the square against the
inclusions commutes on the nose. -/
def mapτ₂ : H.PB.complex ⟶ R.KB :=
  mapτ₂Aux H R φ - Homotopy.nullHomotopicMap
    fun i j => (H.splitting i).r ≫ (ιHomotopy H R φ).hom i j

/-- The square against the inclusions commutes. -/
lemma ι_comp_mapτ₂ : H.ι ≫ mapτ₂ H R φ = mapτ₁ H R φ ≫ R.ι := by
  have hk : (fun i j => H.ι.f i ≫ (H.splitting i).r ≫ (ιHomotopy H R φ).hom i j)
      = (ιHomotopy H R φ).hom := by
    funext i j
    rw [← Category.assoc, (H.splitting i).f_r, Category.id_comp]
  rw [mapτ₂, Preadditive.comp_sub, Homotopy.comp_nullHomotopicMap, hk,
    ← Homotopy.sub_eq_nullHomotopicMap (ιHomotopy H R φ)]
  abel

/-- `mapτ₂` still covers `φ.τ₂`, the correction being null-homotopic. -/
lemma mapτ₂_comm : mapτ₂ H R φ ≫ R.εB = H.PB.π ≫ (ChainComplex.single₀ C).map φ.τ₂ := by
  rw [mapτ₂, Preadditive.sub_comp, nullHomotopicMap_comp_aug, sub_zero, mapτ₂Aux_comm]

/-- The degreewise component of the induced map on the third resolutions, obtained from `mapτ₂`
through the section of the splitting of `H`. -/
def mapτ₃f (n : ℕ) : H.PC.complex.X n ⟶ R.KC.X n :=
  (H.splitting n).s ≫ (mapτ₂ H R φ).f n ≫ R.p.f n

/-- The square against the projections commutes degreewise. -/
lemma p_comp_mapτ₃f (n : ℕ) :
    H.p.f n ≫ mapτ₃f H R φ n = (mapτ₂ H R φ).f n ≫ R.p.f n := by
  have hι : H.ι.f n ≫ (mapτ₂ H R φ).f n = (mapτ₁ H R φ).f n ≫ R.ι.f n := by
    simpa using congr_arg (·.f n) (ι_comp_mapτ₂ H R φ)
  rw [mapτ₃f, ← Category.assoc, (H.splitting n).g_s, Preadditive.sub_comp, Category.id_comp,
    Category.assoc, reassoc_of% hι, R.ι_comp_p_f n]
  simp

/-- The induced map on the third resolutions. -/
def mapτ₃ : H.PC.complex ⟶ R.KC where
  f n := mapτ₃f H R φ n
  comm' i j hij := by
    have hepi : Epi (H.p.f i) := (H.splitting i).epi_g
    rw [← cancel_epi (H.p.f i), ← Category.assoc, p_comp_mapτ₃f, Category.assoc,
      R.p.comm, ← Category.assoc, (mapτ₂ H R φ).comm, Category.assoc,
      ← p_comp_mapτ₃f, ← Category.assoc, ← H.p.comm, Category.assoc]

/-- The square against the projections commutes. -/
lemma p_comp_mapτ₃ : H.p ≫ mapτ₃ H R φ = mapτ₂ H R φ ≫ R.p :=
  HomologicalComplex.hom_ext _ _ (p_comp_mapτ₃f H R φ)

/-- `mapτ₃` covers `φ.τ₃`. -/
lemma mapτ₃_comm : mapτ₃ H R φ ≫ R.εC = H.PC.π ≫ (ChainComplex.single₀ C).map φ.τ₃ := by
  have := Horseshoe.epi_p H
  rw [← cancel_epi H.p, reassoc_of% p_comp_mapτ₃, R.commp, reassoc_of% mapτ₂_comm,
    ← Functor.map_comp, reassoc_of% H.commp, ← Functor.map_comp, φ.comm₂₃]

/-- **A morphism of short complexes lifts a horseshoe into a split sequence of resolutions**, on
the nose. This is `CategoryTheory.ShortComplex.Horseshoe.mapSesHom` with the projectivity of the
target dropped. -/
def mapSesHom : H.ses ⟶ R.ses where
  τ₁ := mapτ₁ H R φ
  τ₂ := mapτ₂ H R φ
  τ₃ := mapτ₃ H R φ
  comm₁₂ := (ι_comp_mapτ₂ H R φ).symm
  comm₂₃ := (p_comp_mapτ₃ H R φ).symm

variable {D : Type u₂} [Category.{v₂} D] [Abelian D] (G : C ⥤ D) [G.Additive]

/-- The image of `mapSesHom` under an additive functor. -/
def mapSesMap : H.mapSes G ⟶ R.mapSes G :=
  (G.mapHomologicalComplex (ComplexShape.down ℕ)).mapShortComplex.map (mapSesHom H R φ)

/-- **The connecting morphisms of the two mapped sequences are intertwined by `mapSesHom`.**
This is the input which, after conjugation by the comparison isomorphisms, says that the
comparison of a left derived functor on two different categories commutes with the connecting
morphisms. -/
lemma δ_naturality (n : ℕ) :
    (H.mapSes_shortExact G).δ (n + 1) n (down_rel_succ n) ≫
        HomologicalComplex.homologyMap (mapSesMap H R φ G).τ₁ n =
      HomologicalComplex.homologyMap (mapSesMap H R φ G).τ₃ (n + 1) ≫
        (R.mapSes_shortExact G).δ (n + 1) n (down_rel_succ n) :=
  HomologicalComplex.HomologySequence.δ_naturality (mapSesMap H R φ G)
    (H.mapSes_shortExact G) (R.mapSes_shortExact G) (n + 1) n (down_rel_succ n)

end Lift

section Transfer

variable [HasProjectiveResolutions C] {S : ShortComplex C} (H : Horseshoe S)
  (R : SplitResolutionSes S) {D : Type u₂} [Category.{v₂} D] [Abelian D] (G : C ⥤ D) [G.Additive]

/-- **The connecting morphism of a horseshoe, transferred along a split sequence of resolutions
of the same short exact sequence.** This is `δ_naturality` with the connecting morphism of the
horseshoe in its conjugated form, which is the form in which the left derived functors carry
it. -/
lemma δ_comp_transfer_aux (n : ℕ) :
    H.δ G n ≫ (H.isoPA G n).hom ≫
        HomologicalComplex.homologyMap (mapSesMap H R (𝟙 S) G).τ₁ n =
      (H.isoPC G (n + 1)).hom ≫
          HomologicalComplex.homologyMap (mapSesMap H R (𝟙 S) G).τ₃ (n + 1) ≫
        (R.mapSes_shortExact G).δ (n + 1) n (down_rel_succ n) := by
  rw [Horseshoe.δ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [δ_naturality]

/-- `δ_comp_transfer_aux` with a further morphism composed on the right. The reassociation is
done here, in the spelling in which the objects are written one way only, because
`Category.assoc` cannot be applied after the restatement below: there the object between the two
factors has the two spellings `(G ∘ W)(K)` and `G(W(K))`, which agree only at default
transparency, so `simp only [Category.assoc]` reports no progress on a goal that prints
exactly. -/
lemma δ_comp_transfer_aux_assoc (n : ℕ) {Z : D}
    (m : HomologicalComplex.homology (R.mapSes G).X₁ n ⟶ Z) :
    H.δ G n ≫ (H.isoPA G n).hom ≫
        HomologicalComplex.homologyMap (mapSesMap H R (𝟙 S) G).τ₁ n ≫ m =
      (H.isoPC G (n + 1)).hom ≫
          HomologicalComplex.homologyMap (mapSesMap H R (𝟙 S) G).τ₃ (n + 1) ≫
        (R.mapSes_shortExact G).δ (n + 1) n (down_rel_succ n) ≫ m := by
  simpa only [Category.assoc] using
    congrArg (fun x => x ≫ m) (δ_comp_transfer_aux H R G n)

/-- `δ_comp_transfer_aux_assoc` in the spelling
`CategoryTheory.ProjectiveResolution.isoLeftDerivedObj` and
`CategoryTheory.Functor.leftDerived_map_eq` use, which is the one in which a comparison of left
derived functors on two categories is stated. The restatement is by `exact` in term mode:
`Horseshoe.isoPA` and `mapSesMap` are `def`s, so the two sides agree only at default
transparency and a `rw` would report no occurrence of a pattern that prints exactly. -/
lemma δ_comp_transfer (n : ℕ) {Z : D}
    (m : (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).obj
      ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.KA) ⟶ Z) :
    H.δ G n ≫ (H.PA.isoLeftDerivedObj G n).hom ≫
        (G.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map
            (mapτ₁ H R (𝟙 S)) ≫ m =
      (H.PC.isoLeftDerivedObj G (n + 1)).hom ≫
          (G.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
            HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) (n + 1)).map
              (mapτ₃ H R (𝟙 S)) ≫
        (R.mapSes_shortExact G).δ (n + 1) n (down_rel_succ n) ≫ m :=
  δ_comp_transfer_aux_assoc H R G n m

end Transfer

end SplitResolutionSes

/-- **A horseshoe is a degreewise split short exact sequence of resolutions.** -/
def Horseshoe.toSplitResolutionSes {S : ShortComplex C} (H : Horseshoe S) :
    SplitResolutionSes S where
  KA := H.PA.complex
  KB := H.PB.complex
  KC := H.PC.complex
  εA := H.PA.π
  εB := H.PB.π
  εC := H.PC.π
  ι := H.ι
  p := H.p
  w := H.w
  splitting := H.splitting
  commι := H.commι
  commp := H.commp

/-- The short complex of complexes carried by a horseshoe, read through
`CategoryTheory.ShortComplex.Horseshoe.toSplitResolutionSes`. -/
lemma Horseshoe.toSplitResolutionSes_ses {S : ShortComplex C} (H : Horseshoe S) :
    H.toSplitResolutionSes.ses = H.ses :=
  rfl

end CategoryTheory.ShortComplex

end
