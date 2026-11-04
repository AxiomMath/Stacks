module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Category.Preorder
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Directed colimits of affine formal algebraic spaces (Stacks 0GVM)

Let `S` be a scheme contained in a big fppf site `B` and let `(X_i)` be a directed system of
affine formal algebraic spaces over `S` whose transition morphisms are representable
thickenings. **Stacks 0GVM** asserts that the colimit `X` of such a system is again an affine
formal algebraic space over `S`.

The content of the lemma is the construction of an affine presentation of `X`. Each stage `X_i`
is a directed colimit of affine schemes `X_{i,ω}` along thickenings. A morphism from an affine
scheme into `X_j` factors through one of the stages of `X_j`, so for `i ≤ j` every
`X_{i,ω} ⟶ X_j` factors through some `X_{j,ω'}`, and that factorization is unique because a
stage maps monomorphically to the space it presents. Ordering the disjoint union
`Ω = ⨿_i Ω_i` by `(i,ω) ≤ (j,ω')` exactly when `X_{i,ω} ⟶ X` factors through `X_{j,ω'} ⟶ X`
therefore turns `Ω` into a directed preorder carrying a diagram of affine schemes with
thickening transition morphisms, and the resulting colimit is `X`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_affinePresentation_of_colimit`: the colimit of such a
  system is a directed colimit of affine schemes over `S` along thickenings.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit`: **Stacks 0GVM**, for a
  colimit which satisfies the set-theoretic condition of Stacks 0AIS.

## Implementation notes

The hypothesis on the transition morphisms is that each is representable and a thickening. This
is the reformulation, recorded in Stacks 0GVL, of the condition that `X_i ⟶ X_j` be a closed
immersion inducing an isomorphism `X_{i,red} ⟶ X_{j,red}`; it is the form the library states,
since it needs no choice of a reduction of each stage.

The set-theoretic condition of Stacks 0AIS is a hypothesis of
`isAffineFormalAlgebraicSpace_colimit` rather than a conclusion. It is not implied by the
hypotheses: it asks for a surjection onto `X` from a sheaf represented by an object of the site,
and the only presentation of `X` at hand is indexed by `Ω`, whose coproduct of stages need not
be bounded by the size cutoff of the site unless the index is small. Stacks 0AIS discharges the
condition for a colimit whose index set is countable, through
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_colimit`.

The reindexing of an iterated colimit along the factorization order is isolated as the
general `isColimit_factorizationCocone`, which uses no property of sheaves: given a colimit
`X` of a diagram `D` and a colimit presentation of each `D.obj i` by a diagram `F i`, together
with the factorization property above, the cocone on the disjoint union of the index categories
ordered by factorization through `X` is a colimit cocone.

## References

* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w t v₁ v₂ u₁ u₂

namespace AlgebraicGeometry.FormalSpace

/-- The category of sheaves of types on the big fppf site of `S` has all colimits indexed by
categories in `Type (u + 1)`. -/
noncomputable local instance sheafHasColimits
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) :=
  Sheaf.instHasColimitsOfSize

/-! ### Colimits along a factorization preorder -/

/-- The preorder on an index type for a family of objects over `Z` in which `p ≤ q` means that
the structure morphism of `A p` factors through that of `A q`. -/
@[instance_reducible] private def factorizationPreorder {C : Type u} [Category.{v} C]
    {K : Type t} {Z : C} (A : K → C) (a : ∀ k, A k ⟶ Z) : Preorder K where
  le p q := ∃ f : A p ⟶ A q, f ≫ a q = a p
  le_refl p := ⟨𝟙 _, by simp⟩
  le_trans p q r hpq hqr := by
    obtain ⟨f, hf⟩ := hpq
    obtain ⟨g, hg⟩ := hqr
    exact ⟨f ≫ g, by simp [Category.assoc, hg, hf]⟩

/-- The diagram on the factorization preorder of a family of monomorphisms into `Z` sending
`p ≤ q` to the unique morphism `A p ⟶ A q` over `Z`. -/
private def factorizationDiagram {C : Type u} [Category.{v} C]
    {K : Type t} {Z : C} (A : K → C) (a : ∀ k, A k ⟶ Z) [∀ k, Mono (a k)] :
    letI := factorizationPreorder A a
    K ⥤ C := by
  letI := factorizationPreorder A a
  exact {
    obj := A
    map f := (leOfHom f).choose
    map_id p :=
      (cancel_mono (a p)).mp ((leOfHom (𝟙 p)).choose_spec.trans (Category.id_comp _).symm)
    map_comp {p q r} f g := by
      apply (cancel_mono (a r)).mp
      simp only [(leOfHom (f ≫ g)).choose_spec, Category.assoc,
        (leOfHom g).choose_spec, (leOfHom f).choose_spec]
  }

/-- The transition morphisms of the factorization diagram lie over `Z`. -/
private theorem factorizationDiagram_map {C : Type u} [Category.{v} C]
    {K : Type t} {Z : C} (A : K → C) (a : ∀ k, A k ⟶ Z) [∀ k, Mono (a k)] :
    letI := factorizationPreorder A a
    ∀ {p q : K} (f : p ⟶ q), (factorizationDiagram A a).map f ≫ a q = a p := by
  let := factorizationPreorder A a
  intro p q f
  exact (leOfHom f).choose_spec

/-- The cocone with vertex `Z` on the factorization diagram given by the structure
morphisms. -/
private def factorizationCocone {C : Type u} [Category.{v} C]
    {K : Type t} {Z : C} (A : K → C) (a : ∀ k, A k ⟶ Z) [∀ k, Mono (a k)] :
    letI := factorizationPreorder A a
    Cocone (factorizationDiagram A a) := by
  letI := factorizationPreorder A a
  exact ⟨Z, {
    app := a
    naturality := fun p q f => by
      exact (factorizationDiagram_map A a f).trans (Category.comp_id _).symm }⟩

/-- An iterated colimit is a colimit over the disjoint union of the inner index categories,
ordered by factorization through the outer colimit: if `cD` is a colimit of `D`, each `D.obj i`
is a colimit of `F i` with monomorphic structure morphisms into `cD.pt`, and every
`(F i).obj x ⟶ D.obj j` arising from `i ⟶ j` factors through some `(F j).obj y`, then the
factorization cocone on `Σ i, J i` is a colimit cocone. -/
private def isColimit_factorizationCocone
    {C : Type u} [Category.{v} C]
    {I : Type t} [Category.{w} I] (D : I ⥤ C)
    (cD : Cocone D) (hD : IsColimit cD)
    (J : I → Type t) [∀ i, Category.{w} (J i)]
    (F : ∀ i, J i ⥤ C)
    (s : ∀ i, F i ⟶ (Functor.const (J i)).obj (D.obj i))
    (hs : ∀ i, IsColimit (Cocone.mk (D.obj i) (s i)))
    (a : ∀ p : Σ i, J i, (F p.1).obj p.2 ⟶ cD.pt)
    (ha : ∀ p, a p = (s p.1).app p.2 ≫ cD.ι.app p.1)
    [∀ p, Mono (a p)]
    (hfactor : ∀ {i j} (f : i ⟶ j) (x : J i),
      ∃ y : J j, ∃ g : (F i).obj x ⟶ (F j).obj y,
        g ≫ (s j).app y = (s i).app x ≫ D.map f) :
    letI := factorizationPreorder (fun p : Σ i, J i => (F p.1).obj p.2) a
    letI : SmallCategory (Σ i, J i) := Preorder.smallCategory _
    IsColimit (factorizationCocone (fun p : Σ i, J i => (F p.1).obj p.2) a) := by
  classical
  let A := fun p : Σ i, J i => (F p.1).obj p.2
  letI := factorizationPreorder A a
  letI : SmallCategory (Σ i, J i) := Preorder.smallCategory _
  let E := factorizationDiagram A a
  have map_eq {p q : Σ i, J i} (f : p ⟶ q) (g : A p ⟶ A q)
      (hg : g ≫ a q = a p) : E.map f = g :=
    (cancel_mono (a q)).mp ((factorizationDiagram_map A a f).trans hg.symm)
  have edge {i j} (f : i ⟶ j) (x : J i) (y : J j)
      (g : (F i).obj x ⟶ (F j).obj y)
      (hg : g ≫ (s j).app y = (s i).app x ≫ D.map f) :
      g ≫ a ⟨j, y⟩ = a ⟨i, x⟩ := by
    rw [ha, ha, ← Category.assoc, hg, Category.assoc, cD.w]
  have internal {i} {x y : J i} (f : x ⟶ y) :
      (F i).map f ≫ a ⟨i, y⟩ = a ⟨i, x⟩ := by
    rw [ha, ha, ← Category.assoc]
    simp
  let restrict (c : Cocone E) (i : I) : Cocone (F i) :=
    ⟨c.pt, { app := fun x => c.ι.app ⟨i, x⟩
             naturality := by
               intro x y f
               let l : (⟨i, x⟩ : Σ i, J i) ⟶ ⟨i, y⟩ :=
                 homOfLE ⟨(F i).map f, internal f⟩
               have h := c.w l
               rw [map_eq l ((F i).map f) (internal f)] at h
               exact h.trans (Category.comp_id _).symm }⟩
  let outer (c : Cocone E) : Cocone D :=
    ⟨c.pt, { app := fun i => (hs i).desc (restrict c i)
             naturality := by
               intro i j f
               apply (hs i).hom_ext
               intro x
               obtain ⟨y, g, hg⟩ := hfactor f x
               let l : (⟨i, x⟩ : Σ i, J i) ⟶ ⟨j, y⟩ :=
                 homOfLE ⟨g, edge f x y g hg⟩
               have h := c.w l
               rw [map_eq l g (edge f x y g hg)] at h
               change (s i).app x ≫ D.map f ≫ (hs j).desc (restrict c j) =
                 (s i).app x ≫ (hs i).desc (restrict c i) ≫ 𝟙 _
               rw [Category.comp_id, ← Category.assoc, ← hg, Category.assoc,
                 (hs j).fac, (hs i).fac]
               exact h }⟩
  refine ⟨fun c => hD.desc (outer c), ?_, ?_⟩
  · intro c p
    change a p ≫ hD.desc (outer c) = c.ι.app p
    rw [ha, Category.assoc, hD.fac]
    exact (hs p.1).fac (restrict c p.1) p.2
  · intro c m hm
    change cD.pt ⟶ c.pt at m
    change ∀ p, a p ≫ m = c.ι.app p at hm
    apply hD.hom_ext
    intro i
    rw [hD.fac]
    apply (hs i).hom_ext
    intro x
    change (s i).app x ≫ cD.ι.app i ≫ m =
      (s i).app x ≫ (hs i).desc (restrict c i)
    rw [← Category.assoc, ← ha ⟨i, x⟩]
    exact (hm ⟨i, x⟩).trans ((hs i).fac (restrict c i) x).symm

/-! ### Thickenings of schemes as a morphism property -/

/-- Thickenings of schemes are stable under composition. -/
theorem isThickening_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) :=
  ⟨fun _ _ hf hg => Stacks.Thickenings.isThickening_comp hf hg⟩

/-- A thickening of objects of the big fppf site of `S` is a monomorphism. -/
private theorem thickening_le_monomorphisms (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) ≤
      MorphismProperty.monomorphisms (BigFppfOver B S hS) := by
  intro U V f hf
  have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map f) := hf.1
  exact Functor.mono_of_mono_map (BigFppfOver.toScheme B S hS) inferInstance

/-- The sheafified Yoneda embedding of the big fppf site of `S` preserves monomorphisms. -/
private theorem preservesMonomorphisms_sheafifiedYoneda (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).PreservesMonomorphisms := by
  let J := BigFppfOver.topology B S hS
  show ((uliftYoneda.{u + 1}) ⋙ presheafToSheaf J (Type (u + 1))).PreservesMonomorphisms
  infer_instance

/-- A morphism of fppf sheaves which is representable and all of whose represented base changes
are monomorphisms of the site is a monomorphism: a section of the source over an object of the
site is a splitting of such a base change, and a monomorphism admits at most one splitting. -/
private theorem mono_of_relative_sheafifiedYoneda (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (P : MorphismProperty (BigFppfOver B S hS))
    (hP : P ≤ MorphismProperty.monomorphisms (BigFppfOver B S hS))
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} {f : X ⟶ Y}
    (hf : MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) P f) :
    Mono f := by
  let J := BigFppfOver.topology B S hS
  have := preservesMonomorphisms_sheafifiedYoneda B S hS
  refine (Sheaf.Hom.mono_iff_presheaf_mono J _ f).2 ((NatTrans.mono_iff_mono_app f.hom).2 ?_)
  intro W
  induction W with
  | op U =>
    rw [CategoryTheory.mono_iff_injective]
    intro x y hxy
    let a : (Sheaf.sheafifiedYoneda J).obj U ⟶ X := (Sheaf.sectionEquiv J).symm x
    let b : (Sheaf.sheafifiedYoneda J).obj U ⟶ X := (Sheaf.sectionEquiv J).symm y
    have hab : a ≫ f = b ≫ f := by
      apply (Sheaf.sectionEquiv J).injective
      rw [Sheaf.sectionEquiv_comp, Sheaf.sectionEquiv_comp]
      simpa only [a, b, Equiv.apply_symm_apply] using hxy
    let g : (Sheaf.sheafifiedYoneda J).obj U ⟶ Y := a ≫ f
    have hp := hf.rep.isPullback g
    have : Mono (hf.rep.snd g) := hP _ (hf.property_snd g)
    have : Mono ((Sheaf.sheafifiedYoneda J).map (hf.rep.snd g)) := inferInstance
    let la := hp.lift a (𝟙 _) (by simp [g])
    let lb := hp.lift b (𝟙 _) (by simpa [g] using hab.symm)
    have hla : la ≫ (Sheaf.sheafifiedYoneda J).map (hf.rep.snd g) = 𝟙 _ :=
      hp.lift_snd _ _ _
    have hlb : lb ≫ (Sheaf.sheafifiedYoneda J).map (hf.rep.snd g) = 𝟙 _ :=
      hp.lift_snd _ _ _
    have hl : la = lb := (cancel_mono _).mp (hla.trans hlb.symm)
    exact (Sheaf.sectionEquiv J).symm.injective <|
      calc
        a = la ≫ hf.rep.fst g := (hp.lift_fst _ _ _).symm
        _ = lb ≫ hf.rep.fst g := by rw [hl]
        _ = b := hp.lift_fst _ _ _

/-- A morphism of fppf sheaves which is representable and a thickening is a
monomorphism. -/
private theorem mono_of_relativeThickening (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} {f : X ⟶ Y}
    (hf : MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) f) :
    Mono f :=
  mono_of_relative_sheafifiedYoneda B S hS _ (thickening_le_monomorphisms B S hS) hf

/-- The colimit injections of a directed system of fppf sheaves whose transition morphisms are
monomorphisms are themselves monomorphisms. -/
private theorem mono_colimit_ι (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    [∀ i j (f : i ⟶ j), Mono (D.map f)] (i : I) : Mono (colimit.ι D i) :=
  (colimit.isColimit D).mono_ι_app_of_isFiltered i

/-- The fully faithful structure of the sheafified Yoneda embedding of the big fppf site
of `S`, which is subcanonical. -/
private def fullyFaithful_sheafifiedYoneda (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).FullyFaithful := by
  let J := BigFppfOver.topology B S hS
  letI : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let e : J.uliftYoneda.{u + 1} ≅ Sheaf.sheafifiedYoneda J :=
    (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (sheafificationNatIso J (Type (u + 1))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (J.uliftYonedaCompSheafToPresheaf) (presheafToSheaf J (Type (u + 1)))
  exact (J.fullyFaithfulUliftYoneda).ofIso e

/-! ### Presentations of a stage by affine schemes -/

/-- A presentation of a sheaf on the big fppf site of `S` as a directed colimit of sheaves
represented by affine schemes over `S` whose transition morphisms are thickenings. -/
private structure AffinePresentation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) where
  /-- The index type of the presentation. -/
  Index : Type (u + 1)
  /-- The preorder on the index type. -/
  preorder : Preorder Index
  /-- The index type is nonempty. -/
  nonempty : Nonempty Index
  /-- The index type is directed. -/
  directed : letI : Preorder Index := preorder; IsDirected Index (· ≤ ·)
  /-- The diagram of affine schemes over `S`. -/
  stages : letI : Preorder Index := preorder; Index ⥤ BigAffineFppf B S hS
  /-- The transition morphisms are thickenings. -/
  stageThickenings : letI : Preorder Index := preorder; ∀ ⦃i j : Index⦄ (f : i ⟶ j),
    Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (stages.map f))
  /-- The sheaf is the colimit of the represented stages. -/
  comparison : letI : Preorder Index := preorder; Nonempty (X ≅ colimit
    (stages ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))

/-- A chosen affine presentation of an affine formal algebraic space. -/
private def affinePresentation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hX : IsAffineFormalAlgebraicSpace B S hS X) : AffinePresentation B S hS X := by
  classical
  let I := Classical.choose hX.2
  have hI' := Classical.choose_spec hX.2
  let pre := Classical.choose hI'
  have hpre := Classical.choose_spec hI'
  letI : Preorder I := pre
  have hD' := hpre.2.2
  let D := Classical.choose hD'
  have hDspec := Classical.choose_spec hD'
  exact ⟨I, pre, hpre.1, hpre.2.1, D, hDspec.1, hDspec.2⟩

/-- The index type of the combined presentation of a colimit: the disjoint union of the index
types of the chosen presentations of the stages. -/
private abbrev CombinedStageIndex (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type (u + 1)} [Preorder I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hD : ∀ i, IsAffineFormalAlgebraicSpace B S hS (D.obj i)) :=
  Σ i : I, (affinePresentation B S hS (D.obj i) (hD i)).Index

/-- The diagram of sheaves represented by the stages of an affine presentation. -/
private def affinePresentationSheafDiagram (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : AffinePresentation B S hS X) :
    letI : Preorder P.Index := P.preorder
    P.Index ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)) := by
  letI : Preorder P.Index := P.preorder
  let J := BigFppfOver.topology B S hS
  let inc := BigAffineFppf.inclusion B S hS
  let y := Sheaf.sheafifiedYoneda.{u, u + 1} J
  exact {
    obj i := y.obj (inc.obj (P.stages.obj i))
    map f := y.map (inc.map (P.stages.map f))
    map_id i := by simp
    map_comp f g := by simp
  }

/-- The chosen identification of a sheaf with the colimit of an affine presentation of it. -/
private def affinePresentationComparison (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : AffinePresentation B S hS X) :
    letI : Preorder P.Index := P.preorder
    X ≅ colimit (affinePresentationSheafDiagram B S hS X P) := by
  letI : Preorder P.Index := P.preorder
  exact Classical.choice P.comparison

/-- The morphism from a stage of an affine presentation to the sheaf it presents. -/
private def affinePresentationStageMap (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : AffinePresentation B S hS X) (i : P.Index) :
    letI : Preorder P.Index := P.preorder
    (affinePresentationSheafDiagram B S hS X P).obj i ⟶ X := by
  letI : Preorder P.Index := P.preorder
  exact colimit.ι (affinePresentationSheafDiagram B S hS X P) i ≫
    (affinePresentationComparison B S hS X P).inv

/-- The stage morphisms of an affine presentation form a cocone. -/
private theorem affinePresentationStageMap_fac (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : AffinePresentation B S hS X) :
    letI : Preorder P.Index := P.preorder
    ∀ {i j : P.Index} (f : i ⟶ j),
    (affinePresentationSheafDiagram B S hS X P).map f ≫
      affinePresentationStageMap B S hS X P j =
    affinePresentationStageMap B S hS X P i := by
  intro i j f
  let : Preorder P.Index := P.preorder
  dsimp [affinePresentationStageMap]
  rw [← Category.assoc, colimit.w]

/-- Each stage of an affine presentation maps to the presented sheaf by a representable
thickening. -/
private theorem affinePresentationStageMap_relativeThickening (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : AffinePresentation B S hS X) (i : P.Index) :
    letI : Preorder P.Index := P.preorder
    MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))
      (affinePresentationStageMap B S hS X P i) := by
  let : Preorder P.Index := P.preorder
  have : Nonempty P.Index := P.nonempty
  have : IsDirected P.Index (· ≤ ·) := P.directed
  exact isThickening_colimitι B S hS P.stages P.stageThickenings X
    (affinePresentationComparison B S hS X P).symm i

/-- Each stage of an affine presentation maps monomorphically to the presented sheaf. -/
private theorem affinePresentationStageMap_mono (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : AffinePresentation B S hS X) (i : P.Index) :
    letI : Preorder P.Index := P.preorder
    Mono (affinePresentationStageMap B S hS X P i) := by
  let : Preorder P.Index := P.preorder
  exact mono_of_relativeThickening B S hS
    (affinePresentationStageMap_relativeThickening B S hS X P i)

/-- The affine scheme over `S` indexed by a point of the combined index. -/
private def combinedStageObject (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type (u + 1)} [Preorder I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hD : ∀ i, IsAffineFormalAlgebraicSpace B S hS (D.obj i))
    (p : CombinedStageIndex B S hS D hD) : BigAffineFppf B S hS :=
  let P := affinePresentation B S hS (D.obj p.1) (hD p.1)
  letI : Preorder P.Index := P.preorder
  P.stages.obj p.2

/-- The morphism from a combined stage to the colimit of the system. -/
private def combinedStageMapToColimit (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type (u + 1)} [Preorder I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hD : ∀ i, IsAffineFormalAlgebraicSpace B S hS (D.obj i))
    (p : CombinedStageIndex B S hS D hD) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj (combinedStageObject B S hS D hD p)) ⟶
      colimit D := by
  let P := affinePresentation B S hS (D.obj p.1) (hD p.1)
  letI : Preorder P.Index := P.preorder
  let F : P.Index ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)) :=
    P.stages ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let eP : D.obj p.1 ≅ colimit F := Classical.choice P.comparison
  change F.obj p.2 ⟶ colimit D
  exact colimit.ι F p.2 ≫ eP.inv ≫ colimit.ι D p.1

/-- The morphism from a combined stage to a sheaf identified with the colimit of the
system. -/
private def combinedStageMap (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type (u + 1)} [Preorder I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hD : ∀ i, IsAffineFormalAlgebraicSpace B S hS (D.obj i))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) (e : X ≅ colimit D)
    (p : CombinedStageIndex B S hS D hD) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj (combinedStageObject B S hS D hD p)) ⟶ X :=
  combinedStageMapToColimit B S hS D hD p ≫ e.inv

/-- A morphism from a sheaf represented by an affine scheme over `S` into an affine formal
algebraic space factors through a stage of any presentation of it. -/
private theorem exists_factor_affine_through_presentation (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {K : Type (u + 1)} [Preorder K] [Nonempty K] [IsDirected K (· ≤ ·)]
    (E : K ⥤ BigAffineFppf B S hS)
    (hE : ∀ ⦃i j : K⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (E.map f)))
    (Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (e : Y ≅ colimit (E ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (T : BigAffineFppf B S hS)
    (f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Y) :
    ∃ i : K, ∃ g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj T) ⟶
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (E.obj i)),
      g ≫ colimit.ι (E ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.inv = f := by
  let J := BigFppfOver.topology B S hS
  let V := (BigAffineFppf.inclusion B S hS).obj T
  let Z := yoneda.obj V
  have hZ : IsAlgebraicSpace B S hS Z := isAlgebraicSpace_yoneda B S hS V
  have hZqc : Space.IsQuasiCompactSpace B S hS Z := by
    refine ⟨V, 𝟙 (yoneda.obj V), ?_, ?_, ?_⟩
    · have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := T.property
      infer_instance
    · let C := BigFppfOver B S hS
      let q := BigFppfOver.toScheme B S hS
      have : HasPullbacks (BigAffineFppf B S hS) := hasPullbacks_bigAffineFppf B S hS
      have : HasPullbacks C := inferInstance
      have : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
      show (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) q).relative yoneda (𝟙 _)
      refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
      intro A C' g fst snd hpb
      have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
      have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
      have : IsIso (q.map snd) := Functor.map_isIso _ _
      show Surjective (q.map snd)
      infer_instance
    · intro W φ hφ
      simpa using hφ
  obtain ⟨i, g, hg⟩ := exists_factor_through_thickening B S hS K E hE Y e Z hZ hZqc f
  exact ⟨i, g, hg⟩

/-- Any two combined stages are dominated by a third: pass to a common stage of the outer
system and factor both through a single stage of its presentation. -/
private theorem combinedStage_exists_upper (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hD : ∀ i, IsAffineFormalAlgebraicSpace B S hS (D.obj i))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) (e : X ≅ colimit D)
    (p q : CombinedStageIndex B S hS D hD) :
    ∃ r : CombinedStageIndex B S hS D hD,
      (∃ f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (combinedStageObject B S hS D hD p)) ⟶
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
            ((BigAffineFppf.inclusion B S hS).obj (combinedStageObject B S hS D hD r)),
        f ≫ combinedStageMap B S hS D hD X e r = combinedStageMap B S hS D hD X e p) ∧
      (∃ f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (combinedStageObject B S hS D hD q)) ⟶
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
            ((BigAffineFppf.inclusion B S hS).obj (combinedStageObject B S hS D hD r)),
        f ≫ combinedStageMap B S hS D hD X e r = combinedStageMap B S hS D hD X e q) := by
  classical
  obtain ⟨k, hpk, hqk⟩ := exists_ge_ge p.1 q.1
  let α : p.1 ⟶ k := homOfLE hpk
  let β : q.1 ⟶ k := homOfLE hqk
  let Pk := affinePresentation B S hS (D.obj k) (hD k)
  let : Preorder Pk.Index := Pk.preorder
  have : Nonempty Pk.Index := Pk.nonempty
  have : IsDirected Pk.Index (· ≤ ·) := Pk.directed
  let Fk := Pk.stages ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let ePk : D.obj k ≅ colimit Fk := Classical.choice Pk.comparison
  have hFk : Fk = Pk.stages ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) := rfl
  have key (p : CombinedStageIndex B S hS D hD) (α : p.1 ⟶ k) :
      ∃ i, ∀ n, i ≤ n → ∃ f, f ≫ combinedStageMap B S hS D hD X e ⟨k, n⟩ =
        combinedStageMap B S hS D hD X e p := by
    let Pp := affinePresentation B S hS (D.obj p.1) (hD p.1)
    let : Preorder Pp.Index := Pp.preorder
    let fp := affinePresentationStageMap B S hS (D.obj p.1) Pp p.2 ≫ D.map α
    obtain ⟨i, g, hg⟩ := exists_factor_affine_through_presentation
      B S hS Pk.stages Pk.stageThickenings (D.obj k) ePk
      (combinedStageObject B S hS D hD p) fp
    refine ⟨i, fun n hn => ⟨g ≫ Fk.map (homOfLE hn), ?_⟩⟩
    have hg' : g ≫ colimit.ι Fk i ≫ ePk.inv = fp := hg
    dsimp [combinedStageMap, combinedStageMapToColimit]
    change (g ≫ Fk.map (homOfLE hn)) ≫ (colimit.ι Fk n ≫ ePk.inv ≫ colimit.ι D k) ≫ e.inv = _
    simp only [Category.assoc, colimit.w_assoc]
    rw [reassoc_of% hg']
    dsimp [fp, affinePresentationStageMap]
    change _ = (colimit.ι (affinePresentationSheafDiagram B S hS (D.obj p.1) Pp) p.2 ≫
      (affinePresentationComparison B S hS (D.obj p.1) Pp).inv ≫ colimit.ι D p.1) ≫ e.inv
    erw [Category.assoc, Category.assoc, colimit.w_assoc D α]
    exact (Category.assoc _ _ _).symm
  obtain ⟨ip, hp⟩ := key p α
  obtain ⟨iq, hq⟩ := key q β
  obtain ⟨n, hpn, hqn⟩ := exists_ge_ge ip iq
  exact ⟨⟨k, n⟩, hp n hpn, hq n hqn⟩

/-- A diagram in a category is isomorphic to one lifted along a fully faithful functor as soon
as its objects are in the image on objects. -/
private theorem exists_liftDiagram {C : Type u₁} [Category.{v₁} C] {E : Type u₂}
    [Category.{v₂} E] {K : Type t} [Category.{w} K] (Y : C ⥤ E) [Y.Full] [Y.Faithful]
    (F : K ⥤ E) (A : K → C) (hA : ∀ k, F.obj k = Y.obj (A k)) :
    ∃ G : K ⥤ C, Nonempty (G ⋙ Y ≅ F) := by
  let e k : Y.obj (A k) ≅ F.obj k := eqToIso (hA k).symm
  let G : K ⥤ C := {
    obj := A
    map {i j} f := Y.preimage ((e i).hom ≫ F.map f ≫ (e j).inv)
    map_id i := by
      apply Y.map_injective
      simp
    map_comp {i j k} f g := by
      apply Y.map_injective
      simp }
  refine ⟨G, ⟨NatIso.ofComponents e ?_⟩⟩
  intro i j f
  dsimp [G]
  simp

/-- The combined presentation of the colimit by the sheaves represented by the stages of the
presentations of the members of the system. -/
private theorem exists_combinedPresentation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hD : ∀ i, IsAffineFormalAlgebraicSpace B S hS (D.obj i))
    (hthick : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
        (MorphismProperty.inverseImage
          (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) (D.map f))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) (e : X ≅ colimit D) :
    ∃ (K : Type (u + 1)) (pre : Preorder K), letI := pre
      Nonempty K ∧ IsDirected K (· ≤ ·) ∧
      ∃ (F : K ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
        (A : K → BigAffineFppf B S hS),
        (∀ p, F.obj p = (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (A p))) ∧
        (∀ ⦃p q : K⦄ (f : p ⟶ q),
          MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
            (MorphismProperty.inverseImage
              (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
              (BigFppfOver.toScheme B S hS)) (F.map f)) ∧
        Nonempty (X ≅ colimit F) := by
  classical
  let P i := affinePresentation B S hS (D.obj i) (hD i)
  let (i : I) : Preorder (P i).Index := (P i).preorder
  let (i : I) : Nonempty (P i).Index := (P i).nonempty
  let (i : I) : IsDirected (P i).Index (· ≤ ·) := (P i).directed
  let K := CombinedStageIndex B S hS D hD
  let T (i : I) := affinePresentationSheafDiagram B S hS (D.obj i) (P i)
  let s (i : I) : T i ⟶ (Functor.const (P i).Index).obj (D.obj i) := {
    app := affinePresentationStageMap B S hS (D.obj i) (P i)
    naturality := fun p q f => by
      simpa using affinePresentationStageMap_fac B S hS (D.obj i) (P i) f }
  have hs (i : I) : IsColimit (Cocone.mk (D.obj i) (s i)) := by
    let ep := affinePresentationComparison B S hS (D.obj i) (P i)
    apply (colimit.isColimit (T i)).ofIsoColimit
    exact Cocone.ext ep.symm (by intro j; simp [s, affinePresentationStageMap, ep, T])
  let a : ∀ p : K, (T p.1).obj p.2 ⟶ colimit D := combinedStageMapToColimit B S hS D hD
  have : ∀ i j (f : i ⟶ j), Mono (D.map f) :=
    fun _ _ f => mono_of_relativeThickening B S hS (hthick f)
  have : ∀ p : K, Mono (a p) := fun p => by
    have := affinePresentationStageMap_mono B S hS (D.obj p.1) (P p.1) p.2
    have := mono_colimit_ι B S hS D p.1
    show Mono (affinePresentationStageMap B S hS (D.obj p.1) (P p.1) p.2 ≫
      colimit.ι D p.1)
    infer_instance
  let A := fun p : K => (T p.1).obj p.2
  let : Preorder K := factorizationPreorder A a
  let : LE K := (factorizationPreorder A a).toLE
  let : SmallCategory K := Preorder.smallCategory _
  let F := factorizationDiagram A a
  have hne : Nonempty K := ⟨⟨Classical.arbitrary I, Classical.arbitrary _⟩⟩
  have hdir : IsDirected K (· ≤ ·) := by
    constructor
    intro p q
    obtain ⟨r, hrp, hrq⟩ := combinedStage_exists_upper B S hS D hD
      (colimit D) (Iso.refl _) p q
    refine ⟨r, ?_, ?_⟩
    · obtain ⟨g, hg⟩ := hrp
      change A p ⟶ A r at g
      refine ⟨g, ?_⟩
      change g ≫ (a r ≫ 𝟙 _) = a p ≫ 𝟙 _ at hg
      simpa only [Category.comp_id] using hg
    · obtain ⟨g, hg⟩ := hrq
      change A q ⟶ A r at g
      refine ⟨g, ?_⟩
      change g ≫ (a r ≫ 𝟙 _) = a q ≫ 𝟙 _ at hg
      simpa only [Category.comp_id] using hg
  have hc : IsColimit (factorizationCocone A a) := by
    apply isColimit_factorizationCocone D (colimit.cocone D) (colimit.isColimit D)
      (fun i => (P i).Index) T s hs a
    · intro p
      rfl
    · intro i j f x
      obtain ⟨y, g, hg⟩ := exists_factor_affine_through_presentation B S hS
        (P j).stages (P j).stageThickenings (D.obj j)
        (affinePresentationComparison B S hS (D.obj j) (P j))
        ((P i).stages.obj x) ((s i).app x ≫ D.map f)
      exact ⟨y, g, hg⟩
  have hmaps : ∀ ⦃p q : K⦄ (f : p ⟶ q),
      MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
        (MorphismProperty.inverseImage
          (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) (F.map f) := by
    intro p q f
    obtain ⟨k, hpk, hqk⟩ := exists_ge_ge p.1 q.1
    let α : p.1 ⟶ k := homOfLE hpk
    let β : q.1 ⟶ k := homOfLE hqk
    let bp : F.obj p ⟶ D.obj k := (s p.1).app p.2 ≫ D.map α
    let bq : F.obj q ⟶ D.obj k := (s q.1).app q.2 ≫ D.map β
    let ff := fullyFaithful_sheafifiedYoneda B S hS
    have := ff.full
    have := ff.faithful
    have := isThickening_isStableUnderComposition.{u}
    let Q := MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
    have := MorphismProperty.IsStableUnderComposition.inverseImage
      (P := (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS)
    have hbp : Q.relative
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) bp :=
      (Q.relative _).comp_mem _ _
        (affinePresentationStageMap_relativeThickening B S hS _ (P p.1) p.2) (hthick α)
    have : Mono bq := by
      have := affinePresentationStageMap_mono B S hS _ (P q.1) q.2
      show Mono (affinePresentationStageMap B S hS _ (P q.1) q.2 ≫ D.map β)
      infer_instance
    have heq : F.map f ≫ bq = bp := by
      have := mono_colimit_ι B S hS D k
      apply (cancel_mono (colimit.ι D k)).mp
      have hbq : bq ≫ colimit.ι D k = a q := by
        show ((s q.1).app q.2 ≫ D.map β) ≫ colimit.ι D k = a q
        rw [Category.assoc, colimit.w]
        rfl
      have hbp : bp ≫ colimit.ι D k = a p := by
        show ((s p.1).app p.2 ≫ D.map α) ≫ colimit.ι D k = a p
        rw [Category.assoc, colimit.w]
        rfl
      rw [Category.assoc, hbq, hbp]
      exact factorizationDiagram_map A a f
    have hpull : IsPullback (𝟙 (F.obj p)) (F.map f) bp bq :=
      IsPullback.of_horiz_isIso_mono ⟨by simpa using heq.symm⟩
    exact Q.relative_isStableUnderBaseChange.of_isPullback hpull hbp
  refine ⟨K, inferInstance, hne, hdir, F, combinedStageObject B S hS D hD, ?_, hmaps, ?_⟩
  · exact fun _ => rfl
  · exact ⟨e.trans (hc.coconePointUniqueUpToIso (colimit.isColimit F))⟩

/-! ### The colimit of a system of affine formal algebraic spaces -/

/-- The colimit of a directed system of affine formal algebraic spaces over `S` whose
transition morphisms are representable thickenings is a directed colimit of affine schemes
over `S` along thickenings. -/
theorem exists_affinePresentation_of_colimit (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hD : ∀ i, IsAffineFormalAlgebraicSpace B S hS (D.obj i))
    (hthick : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
        (MorphismProperty.inverseImage
          (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) (D.map f))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) (e : X ≅ colimit D) :
    ∃ (K : Type (u + 1)) (pre : Preorder K), letI := pre
      Nonempty K ∧ IsDirected K (· ≤ ·) ∧
      ∃ F : K ⥤ BigAffineFppf B S hS,
        (∀ ⦃p q : K⦄ (f : p ⟶ q), Stacks.Thickenings.IsThickening
          ((BigAffineFppf.toScheme B S hS).map (F.map f))) ∧
        Nonempty (X ≅ colimit (F ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) := by
  obtain ⟨K, pre, hne, hdir, F, A, hA, hF, ⟨eF⟩⟩ :=
    exists_combinedPresentation B S hS D hD hthick X e
  let : Preorder K := pre
  let ff := fullyFaithful_sheafifiedYoneda B S hS
  have := ff.full
  have := ff.faithful
  let Y := BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  obtain ⟨G, ⟨eG⟩⟩ := exists_liftDiagram Y F A hA
  refine ⟨K, pre, hne, hdir, G, ?_, ⟨eF.trans (HasColimit.isoOfNatIso eG.symm)⟩⟩
  intro p q f
  let Q := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hg : Q.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (Y.map (G.map f)) :=
    (MorphismProperty.arrow_mk_iso_iff (P := Q.relative _)
      (Arrow.isoMk (eG.app p) (eG.app q) (eG.hom.naturality f).symm)).mpr (hF f)
  exact hg.property (𝟙 _) (𝟙 _)
    ((BigAffineFppf.inclusion B S hS).map (G.map f)) IsPullback.of_id_fst

/-- The colimit of a directed system of affine formal algebraic spaces over `S` whose transition
morphisms are representable thickenings -- equivalently, closed immersions inducing isomorphisms
on reductions -- is an affine formal algebraic space over `S`, provided it satisfies the
set-theoretic condition of Stacks 0AIS. -/
@[stacks 0GVM "granting the set-theoretic condition of Stacks 0AIS for the colimit"]
theorem isAffineFormalAlgebraicSpace_colimit (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hD : ∀ i, IsAffineFormalAlgebraicSpace B S hS (D.obj i))
    (hthick : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
        (MorphismProperty.inverseImage
          (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) (D.map f))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) (e : X ≅ colimit D)
    (hset : SatisfiesSetTheoreticCondition B S hS X) :
    IsAffineFormalAlgebraicSpace B S hS X := by
  obtain ⟨K, pre, hne, hdir, F, hF, heF⟩ :=
    exists_affinePresentation_of_colimit B S hS D hD hthick X e
  exact ⟨hset, K, pre, hne, hdir, F, hF, heF⟩

end AlgebraicGeometry.FormalSpace

end
