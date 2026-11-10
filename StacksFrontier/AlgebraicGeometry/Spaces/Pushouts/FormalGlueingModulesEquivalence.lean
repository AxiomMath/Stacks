module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFlatBaseChangeQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# The comparison maps of formal glueing of modules (towards Stacks 0AF0)

Stacks 0AF0 says that in Situation 0AEV the functor of Stacks 0AEW is an equivalence, with
quasi-inverse the functor of Stacks 0AEX.  Both are in
`FormalGlueingModulesUnconditional.lean`, together with the adjunction of Stacks 0AEY between
them.  This file proves the parts of the source's argument that do not need the local algebra
at the points of `f⁻¹(Z)`.

* **`γ` is invertible** (`isIso_glueingKernel_counit_left`): restriction to `U` is exact, and by
  flat base change along the open immersion `j` (Stacks 073K in degree zero) it inverts the
  second canonical map of Stacks 0AEX, hence the first projection of the kernel; `j^*j_*` is the
  identity on `𝒪_U`-modules.
* **`β` is invertible over `V`** (`isIso_openImmersionOver_map_homEquiv_symm_glueingKernelSnd`):
  the counit is a morphism of glueing triples.
* **The functor of Stacks 0AEW reflects isomorphisms**
  (`reflectsIsomorphisms_glueingModulesFunctor`): at the points of `U` by restriction, and at
  the points of `Z` because they come from points of `f⁻¹(Z)`, at which `f` is flat, so that the
  fibre of the pullback is a faithfully flat base change.
* **The reduction** (`isIso_glueingAdjunction_unit_counit_of_fiber`): the unit and the counit of
  Stacks 0AEY are invertible as soon as `β` is invertible on the fibres at the points of
  `f⁻¹(Z)`.  That last check is the local algebra of the source's last paragraph.

## Implementation notes

The counit of the restricted adjunction is handled through abstract lemmas
(`CategoryTheory.Adjunction.isIso_toCommaPullbackAdjunctionRestrict_counit_app`,
`CategoryTheory.Adjunction.isIso_map_toCommaPullbackAdjunction_counit_right`) and through the
two components `CategoryTheory.Adjunction.commaCounitLeft` and
`CategoryTheory.Adjunction.commaCounitRight`, instantiated at the formal glueing data and never
unfolded at the concrete categories of modules.  Comparing the concrete spellings of
the same morphism (for example `D.ambientDirectImage` against `Comma.snd _ _ ⋙ f_*`, or the
category instance an abstract lemma unifies against the one instance search finds) exhausts the
elaborator's or the kernel's budget.  The restricted counit lemma therefore takes the
adjunction as an argument with its defining equation, and its full-subcategory types are passed
by name.

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 0AEY](https://stacks.math.columbia.edu/tag/0AEY)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace Comma

variable {A : Type u₁} [Category.{v₁} A] {Bb : Type u₂} [Category.{v₂} Bb]
    {T : Type u₃} [Category.{v₃} T] {L : A ⥤ T} {R : Bb ⥤ T}

/-- A morphism of a comma category whose two components are invertible is invertible. -/
theorem isIso_of_isIso_left_right {X Y : Comma L R} (e : X ⟶ Y) [IsIso e.left]
    [IsIso e.right] : IsIso e :=
  (Comma.isoMk (asIso e.left) (asIso e.right) (by simp)).isIso_hom

end Comma

namespace Adjunction

variable {E : Type u₁} [Category.{v₁} E] {A : Type u₂} [Category.{v₂} A]
    {Bb : Type u₃} [Category.{v₃} Bb] {T : Type u₄} [Category.{v₄} T]
    {F : E ⥤ A} {F' : A ⥤ E} {G : E ⥤ Bb} {G' : Bb ⥤ E}
    {L : A ⥤ T} {L' : T ⥤ A} {R : Bb ⥤ T} {R' : T ⥤ Bb} {N : E ⥤ T} {N' : T ⥤ E}

/-- The transpose of the first projection out of the pullback: the left component of the counit
of `toCommaPullbackAdjunction`. -/
def commaCounitLeft (adjF : F ⊣ F') {K : Comma L R ⥤ E} (κ₁ : K ⟶ Comma.fst L R ⋙ F')
    (X : Comma L R) : F.obj (K.obj X) ⟶ X.left :=
  (adjF.homEquiv (K.obj X) X.left).symm (κ₁.app X)

/-- The transpose of the second projection out of the pullback: the right component of the
counit of `toCommaPullbackAdjunction`. -/
def commaCounitRight (adjG : G ⊣ G') {K : Comma L R ⥤ E} (κ₂ : K ⟶ Comma.snd L R ⋙ G')
    (X : Comma L R) : G.obj (K.obj X) ⟶ X.right :=
  (adjG.homEquiv (K.obj X) X.right).symm (κ₂.app X)

/-- The counit of the restricted adjunction of `toCommaPullbackAdjunctionRestrict` is invertible
at a glueing object as soon as the transposes of the two projections out of the pullback are. -/
theorem isIso_toCommaPullbackAdjunctionRestrict_counit_app [HasPullbacks E]
    (adjF : F ⊣ F') (adjG : G ⊣ G')
    (adjL : L ⊣ L') (adjR : R ⊣ R') (adjN : N ⊣ N') (cF : F ⋙ L ≅ N) (cG : G ⋙ R ≅ N)
    {N'mid : T ⥤ E} (pFmid : L' ⋙ F' ≅ N'mid) (eN : N'mid ⟶ N') (pG : R' ⋙ G' ≅ N')
    (hpF : conjugateEquiv (adjF.comp adjL) adjN cF.inv = pFmid.hom ≫ eN)
    (hpG : conjugateEquiv (adjG.comp adjR) adjN cG.inv = pG.hom)
    (αIso : F ⋙ L ≅ G ⋙ R)
    (hα : ∀ M, αIso.hom.app M = cF.hom.app M ≫ cG.inv.app M)
    {r : Comma.fst L R ⋙ F' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    {s : Comma.snd L R ⋙ G' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    (hr : r = Functor.whiskerRight (Functor.whiskerLeft (Comma.fst L R) adjL.unit) F' ≫
      Functor.whiskerLeft (Comma.fst L R ⋙ L) pFmid.hom ≫
      Functor.whiskerRight (Comma.natTrans L R) N'mid ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) eN)
    (hs : s = Functor.whiskerRight (Functor.whiskerLeft (Comma.snd L R) adjR.unit) G' ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) pG.hom)
    {K : Comma L R ⥤ E} {κ₁ : K ⟶ Comma.fst L R ⋙ F'} {κ₂ : K ⟶ Comma.snd L R ⋙ G'}
    (hKnat : IsPullback κ₁ κ₂ r s)
    {E₀ : Type u₅} [Category.{v₅} E₀] {iE : E₀ ⥤ E} (ffE : iE.FullyFaithful)
    {Q : Type u₆} [Category.{v₆} Q] {iQ : Q ⥤ Comma L R} (ffQ : iQ.FullyFaithful)
    {Lq : E₀ ⥤ Q} {Rq : Q ⥤ E₀}
    (cq : (iE ⋙ F) ⋙ L ≅ (iE ⋙ G) ⋙ R) (hcq : cq = Functor.isoWhiskerLeft iE αIso)
    (comm₁ : Lq ⋙ iQ = Functor.toComma (iE ⋙ F) (iE ⋙ G) cq.hom)
    (comm₂ : iQ ⋙ K = Rq ⋙ iE) (adj : Lq ⊣ Rq)
    (hadj : adj = toCommaPullbackAdjunctionRestrict adjF adjG adjL adjR adjN cF cG pFmid eN pG
      hpF hpG αIso hα hr hs hKnat ffE ffQ cq hcq comm₁ comm₂)
    (t : Q) (X : Comma L R) (hX : iQ.obj t = X)
    (h₁ : IsIso (commaCounitLeft adjF κ₁ X)) (h₂ : IsIso (commaCounitRight adjG κ₂ X)) :
    IsIso (adj.counit.app t) := by
  subst hX hadj
  have h0 : IsIso ((toCommaPullbackAdjunction adjF adjG adjL adjR adjN cF cG pFmid eN pG hpF hpG
      (α := αIso.hom) hα hr hs hKnat).counit.app (iQ.obj t)) := by
    have hl : IsIso ((toCommaPullbackAdjunction adjF adjG adjL adjR adjN cF cG pFmid eN pG hpF
        hpG (α := αIso.hom) hα hr hs hKnat).counit.app (iQ.obj t)).left := by
      change IsIso ((adjF.homEquiv _ _).symm (𝟙 _ ≫ κ₁.app (iQ.obj t)))
      rwa [Category.id_comp]
    have hr' : IsIso ((toCommaPullbackAdjunction adjF adjG adjL adjR adjN cF cG pFmid eN pG hpF
        hpG (α := αIso.hom) hα hr hs hKnat).counit.app (iQ.obj t)).right := by
      change IsIso ((adjG.homEquiv _ _).symm (𝟙 _ ≫ κ₂.app (iQ.obj t)))
      rwa [Category.id_comp]
    exact Comma.isIso_of_isIso_left_right _
  have : IsIso (iQ.map ((toCommaPullbackAdjunctionRestrict adjF adjG adjL adjR adjN cF cG pFmid
      eN pG hpF hpG αIso hα hr hs hKnat ffE ffQ cq hcq comm₁ comm₂).counit.app t)) := by
    rw [toCommaPullbackAdjunctionRestrict, map_restrictFullyFaithful_counit_app]
    infer_instance
  exact ffQ.isIso_of_isIso_map _

/-- **The commutative square carried by the counit.**  The counit of
`toCommaPullbackAdjunction` at a comma object `T` is a morphism of comma objects, whose two
components are the transposes of the two projections out of the pullback; the square it carries
is this one. -/
theorem toCommaPullbackAdjunction_counit_w [HasPullbacks E]
    (adjF : F ⊣ F') (adjG : G ⊣ G') (adjL : L ⊣ L')
    (adjR : R ⊣ R') (adjN : N ⊣ N') (cF : F ⋙ L ≅ N) (cG : G ⋙ R ≅ N)
    {N'mid : T ⥤ E} (pFmid : L' ⋙ F' ≅ N'mid) (eN : N'mid ⟶ N') (pG : R' ⋙ G' ≅ N')
    (hpF : conjugateEquiv (adjF.comp adjL) adjN cF.inv = pFmid.hom ≫ eN)
    (hpG : conjugateEquiv (adjG.comp adjR) adjN cG.inv = pG.hom)
    {α : F ⋙ L ⟶ G ⋙ R} (hα : ∀ M, α.app M = cF.hom.app M ≫ cG.inv.app M)
    {r : Comma.fst L R ⋙ F' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    {s : Comma.snd L R ⋙ G' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    (hr : r = Functor.whiskerRight (Functor.whiskerLeft (Comma.fst L R) adjL.unit) F' ≫
      Functor.whiskerLeft (Comma.fst L R ⋙ L) pFmid.hom ≫
      Functor.whiskerRight (Comma.natTrans L R) N'mid ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) eN)
    (hs : s = Functor.whiskerRight (Functor.whiskerLeft (Comma.snd L R) adjR.unit) G' ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) pG.hom)
    {K : Comma L R ⥤ E} {κ₁ : K ⟶ Comma.fst L R ⋙ F'} {κ₂ : K ⟶ Comma.snd L R ⋙ G'}
    (hKnat : IsPullback κ₁ κ₂ r s) (X : Comma L R) :
    L.map (commaCounitLeft adjF κ₁ X) ≫ X.hom =
      α.app (K.obj X) ≫ R.map (commaCounitRight adjG κ₂ X) := by
  have h := ((toCommaPullbackAdjunction adjF adjG adjL adjR adjN cF cG pFmid eN pG hpF hpG
    hα hr hs hKnat).counit.app X).w
  change L.map ((adjF.homEquiv _ _).symm (𝟙 _ ≫ κ₁.app X)) ≫ X.hom =
    α.app (K.obj X) ≫ R.map ((adjG.homEquiv _ _).symm (𝟙 _ ≫ κ₂.app X)) at h
  unfold commaCounitLeft commaCounitRight
  simp only [Category.id_comp] at h
  exact h

/-- **The right component of the counit, restricted along `R`, is invertible once the left one
is.**  This is the commutative square carried by the counit, read with invertible structure
arrows. -/
theorem isIso_map_toCommaPullbackAdjunction_counit_right [HasPullbacks E]
    (adjF : F ⊣ F') (adjG : G ⊣ G') (adjL : L ⊣ L')
    (adjR : R ⊣ R') (adjN : N ⊣ N') (cF : F ⋙ L ≅ N) (cG : G ⋙ R ≅ N)
    {N'mid : T ⥤ E} (pFmid : L' ⋙ F' ≅ N'mid) (eN : N'mid ⟶ N') (pG : R' ⋙ G' ≅ N')
    (hpF : conjugateEquiv (adjF.comp adjL) adjN cF.inv = pFmid.hom ≫ eN)
    (hpG : conjugateEquiv (adjG.comp adjR) adjN cG.inv = pG.hom)
    (αIso : F ⋙ L ≅ G ⋙ R) (hα : ∀ M, αIso.hom.app M = cF.hom.app M ≫ cG.inv.app M)
    {r : Comma.fst L R ⋙ F' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    {s : Comma.snd L R ⋙ G' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    (hr : r = Functor.whiskerRight (Functor.whiskerLeft (Comma.fst L R) adjL.unit) F' ≫
      Functor.whiskerLeft (Comma.fst L R ⋙ L) pFmid.hom ≫
      Functor.whiskerRight (Comma.natTrans L R) N'mid ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) eN)
    (hs : s = Functor.whiskerRight (Functor.whiskerLeft (Comma.snd L R) adjR.unit) G' ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) pG.hom)
    {K : Comma L R ⥤ E} {κ₁ : K ⟶ Comma.fst L R ⋙ F'} {κ₂ : K ⟶ Comma.snd L R ⋙ G'}
    (hKnat : IsPullback κ₁ κ₂ r s) (X : Comma L R) (hX : IsIso X.hom)
    (h₁ : IsIso (commaCounitLeft adjF κ₁ X)) :
    IsIso (R.map (commaCounitRight adjG κ₂ X)) := by
  have h := toCommaPullbackAdjunction_counit_w adjF adjG adjL adjR adjN cF cG pFmid eN pG hpF hpG
    hα hr hs hKnat X
  have h4 : IsIso (L.map (commaCounitLeft adjF κ₁ X) ≫ X.hom) :=
    inferInstance
  rw [h] at h4
  exact IsIso.of_isIso_comp_left (αIso.hom.app (K.obj X)) _

/-- Invertibility of a component of the counit does not depend on the adjunction: two
adjunctions between the same functors have counits differing by the unique comparison of the
right adjoints. -/
theorem isIso_counit_app_of_isIso_counit_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {Lf : C ⥤ D} {Rf : D ⥤ C} (adj₁ adj₂ : Lf ⊣ Rf) (Y : D)
    (h : IsIso (adj₁.counit.app Y)) : IsIso (adj₂.counit.app Y) := by
  have e := congrArg (fun α => NatTrans.app α Y) (rightAdjointUniq_hom_counit adj₁ adj₂)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at e
  rw [← e] at h
  exact IsIso.of_isIso_comp_left (Lf.map ((rightAdjointUniq adj₁ adj₂).hom.app Y))
    (adj₂.counit.app Y)

/-- An adjunction whose counit is invertible and whose left adjoint reflects isomorphisms has an
invertible unit: by the triangle identity the left adjoint of the unit is the inverse of the
counit. -/
theorem isIso_unit_app_of_isIso_counit {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {Lf : C ⥤ D} {Rf : D ⥤ C} (adj : Lf ⊣ Rf) [Lf.ReflectsIsomorphisms]
    (h : ∀ Y, IsIso (adj.counit.app Y)) (X : C) : IsIso (adj.unit.app X) := by
  have : IsIso (Lf.map (adj.unit.app X)) := by
    have := h (Lf.obj X)
    have : IsIso (Lf.map (adj.unit.app X) ≫ adj.counit.app (Lf.obj X)) := by
      rw [adj.left_triangle_components X]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app (Lf.obj X))
  exact isIso_of_reflects_iso _ Lf

end Adjunction

/-- `J` inverts a component of a composite of natural transformations when it inverts the
component of the first factor and the second factor is invertible there. -/
theorem isIso_map_comp_app {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E]
    {E' : Type u₃} [Category.{v₃} E'] {A M N : C ⥤ E} {s : A ⟶ N} {a : A ⟶ M} {b : M ⟶ N}
    (hs : s = a ≫ b) (J : E ⥤ E')
    (t : C) (ha : IsIso (J.map (a.app t))) (hb : IsIso (b.app t)) :
    IsIso (J.map (s.app t)) := by
  subst hs
  rw [NatTrans.comp_app, Functor.map_comp]
  infer_instance

/-- `J` inverts a component of a right whiskering `F ∘ α` when it inverts `F` of the component
of `α`. -/
theorem isIso_map_whiskerRight_whiskerLeft_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']
    {X Y : D ⥤ D} (P : C ⥤ D) (α : X ⟶ Y) (F : D ⥤ E) (J : E ⥤ E') (t : C)
    (h : IsIso ((F ⋙ J).map (α.app (P.obj t)))) :
    IsIso (J.map ((Functor.whiskerRight (Functor.whiskerLeft P α) F).app t)) :=
  h

/-- A component of a whiskered composite `F(η_P) ≫ c` with `c` invertible is inverted by a functor
`J` as soon as `J(F(η_P))` is.  Stated over abstract categories so that the reduction of the
whiskerings happens there and not at a concrete category of modules. -/
theorem isIso_map_app_of_eq_whisker {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {V : Type u₃} [Category.{v₃} V] {E : Type u₄} [Category.{v₄} E]
    {E' : Type u₅} [Category.{v₅} E'] (P : C ⥤ D) (pl : D ⥤ V) (ps : V ⥤ D)
    (η : 𝟭 D ⟶ pl ⋙ ps) (F : D ⥤ E) (Ht : V ⥤ E) (c : ps ⋙ F ≅ Ht)
    (J : E ⥤ E') (t : C) (h : IsIso ((F ⋙ J).map (η.app (P.obj t)))) :
    IsIso (J.map ((Functor.whiskerRight (Functor.whiskerLeft P η) F ≫
      Functor.whiskerLeft (P ⋙ pl) c.hom).app t)) := by
  have h' : IsIso (J.map (F.map (η.app (P.obj t)))) := h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp]
  infer_instance

/-- A morphism `a` is inverted by a functor `F` as soon as a natural transformation `F ⟶ M ⋙ N`
is invertible at both ends of `a` and `M` inverts `a`. -/
theorem isIso_map_of_natTrans {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E]
    {V : Type u₃} [Category.{v₃} V] (F : C ⥤ E) (M : C ⥤ V) (N : V ⥤ E) (β : F ⟶ M ⋙ N)
    (x y : C) (a : x ⟶ y) (hx : IsIso (β.app x)) (hy : IsIso (β.app y)) (ha : IsIso (M.map a)) :
    IsIso (F.map a) := by
  have : IsIso (F.map a ≫ β.app y) := by
    rw [β.naturality a]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hx (Functor.map_isIso N (M.map a))
  exact IsIso.of_isIso_comp_right _ (β.app y)

end CategoryTheory

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : FormalGlueingSituation B S hS)

/-- The glueing square `V ⟶ Y`, `V ⟶ U`, `U ⟶ X`, `Y ⟶ X` is cartesian in the category of
algebraic spaces: `V` is the inverse image of `U`. -/
theorem isPullback_glueingSquare :
    IsPullback D.openImmersionOver D.overlapRestriction D.ambientMorphism D.openImmersion :=
  (IsPullback.of_map_of_faithful (ObjectProperty.ι _)
    (show IsPullback ((ObjectProperty.ι _).map D.overlapRestriction)
      ((ObjectProperty.ι _).map D.openImmersionOver) ((ObjectProperty.ι _).map D.openImmersion)
      ((ObjectProperty.ι _).map D.ambientMorphism) from
      Subfunctor.isPullback_preimage D.f D.U)).flip

/-- The morphism `j : U ⟶ X` is an open immersion of algebraic spaces. -/
theorem isOpenImmersion_openImmersion : IsOpenImmersion B S hS D.openImmersion.hom :=
  D.isOpenSubspace_U.2

/-- The morphism `j' : V ⟶ Y` is an open immersion of algebraic spaces. -/
theorem isOpenImmersion_openImmersionOver : IsOpenImmersion B S hS D.openImmersionOver.hom :=
  D.isOpenSubspace_V.2

/-- The open immersion `j : U ⟶ X` is flat. -/
theorem isFlat_openImmersion : IsFlat B S hS D.openImmersion.hom :=
  isFlat_of_isEtale B S hS (isEtale_of_isOpenImmersion B S hS D.isOpenImmersion_openImmersion)

/-- For an `𝒪_U`-module `H`, the counit `j^*j_*H ⟶ H` of the adjunction `j^* ⊣ j_*` along the
open immersion `j : U ⟶ X` is an isomorphism. -/
instance isIso_counit_openImmersion (H : Modules.{u, u} B S hS D.spaceU.1 D.spaceU.2) :
    IsIso ((modulePullbackAdjunction B S hS D.openImmersion).counit.app H) :=
  have := (fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS _
    D.isOpenImmersion_openImmersion).full
  have := (fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS _
    D.isOpenImmersion_openImmersion).faithful
  inferInstance

/-- For an `𝒪_V`-module `H`, the counit `j'^*j'_*H ⟶ H` of the adjunction `j'^* ⊣ j'_*` along
the open immersion `j' : V ⟶ Y` is an isomorphism. -/
instance isIso_counit_openImmersionOver (H : Modules.{u, u} B S hS D.spaceV.1 D.spaceV.2) :
    IsIso ((modulePullbackAdjunction B S hS D.openImmersionOver).counit.app H) :=
  have := (fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS _
    D.isOpenImmersion_openImmersionOver).full
  have := (fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS _
    D.isOpenImmersion_openImmersionOver).faithful
  inferInstance

/-- The restriction to `V` of the unit `G ⟶ j'_*(G|_V)` is invertible, by the triangle identity,
the counit along the open immersion `j'` being invertible. -/
instance isIso_modulePullback_map_unit_openImmersionOver
    (G : Modules.{u, u} B S hS D.spaceY.1 D.spaceY.2) :
    IsIso ((modulePullback B S hS D.openImmersionOver).map
      ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app G)) := by
  have : IsIso ((modulePullback B S hS D.openImmersionOver).map
      ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app G) ≫
        (modulePullbackAdjunction B S hS D.openImmersionOver).counit.app
          ((modulePullback B S hS D.openImmersionOver).obj G)) := by
    rw [(modulePullbackAdjunction B S hS D.openImmersionOver).left_triangle_components G]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _
    ((modulePullbackAdjunction B S hS D.openImmersionOver).counit.app
      ((modulePullback B S hS D.openImmersionOver).obj G))

/-- For a quasi-coherent `𝒪_Y`-module `G`, the base change map `j^*f_*G ⟶ (f|_V)_*(G|_V)` of the
glueing square is an isomorphism. -/
theorem testH1 (G : Modules.{u, u} B S hS D.spaceY.1 D.spaceY.2) (hG : G.IsQuasicoherentOnSite) :
    IsIso ((moduleBaseChangeMap D.ambientMorphism D.openImmersion
      D.overlapRestriction D.openImmersionOver D.isPullback_glueingSquare.w).app ((𝟭 _).obj G)) :=
  isIso_moduleBaseChangeMap_app_of_isFlat D.isPullback_glueingSquare D.quasiCompact_f
    D.quasiSeparated_f D.isFlat_openImmersion ((𝟭 _).obj G) hG

/-- For a quasi-coherent `𝒪_Y`-module `G`, the base change map of the glueing square at the
module `j'_*(G|_V)` is an isomorphism. -/
theorem testH2 (G : Modules.{u, u} B S hS D.spaceY.1 D.spaceY.2) (hG : G.IsQuasicoherentOnSite) :
    IsIso ((moduleBaseChangeMap D.ambientMorphism D.openImmersion
      D.overlapRestriction D.openImmersionOver D.isPullback_glueingSquare.w).app
        ((modulePullback B S hS D.openImmersionOver ⋙
          modulePushforward B S hS D.openImmersionOver).obj G)) :=
  isIso_moduleBaseChangeMap_app_of_isFlat D.isPullback_glueingSquare D.quasiCompact_f
    D.quasiSeparated_f D.isFlat_openImmersion _
    (isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS D.openImmersionOver
      D.isQuasiCompact_openImmersionOver D.isQuasiSeparated_openImmersionOver _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        D.openImmersionOver G hG))

/-- **Flat base change along `j` inverts `f_*` of the unit along `j'`.**  For a quasi-coherent
`𝒪_Y`-module `G`, `j^*f_*(G ⟶ j'_*(G|_V))` is invertible: by flat base change along the open
immersion `j` (Stacks 073K in degree zero, for the quasi-coherent modules `G` and `j'_*(G|_V)`)
it is `(f|_V)_*` of the restriction of that unit to `V`, which is invertible. -/
theorem isIso_modulePullback_openImmersion_map_pushforward_unit
    (G : Modules.{u, u} B S hS D.spaceY.1 D.spaceY.2) (hG : G.IsQuasicoherentOnSite) :
    IsIso ((modulePushforward B S hS D.ambientMorphism ⋙
      modulePullback B S hS D.openImmersion).map
        ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app G)) :=
  isIso_map_of_natTrans (modulePushforward B S hS D.ambientMorphism ⋙
      modulePullback B S hS D.openImmersion) (modulePullback B S hS D.openImmersionOver)
      (modulePushforward B S hS D.overlapRestriction)
      (moduleBaseChangeMap D.ambientMorphism D.openImmersion
        D.overlapRestriction D.openImmersionOver D.isPullback_glueingSquare.w) ((𝟭 _).obj G)
      ((modulePullback B S hS D.openImmersionOver ⋙
          modulePushforward B S hS D.openImmersionOver).obj G)
      ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app G) (D.testH1 G hG)
      (D.testH2 G hG) (D.isIso_modulePullback_map_unit_openImmersionOver G)

/-- **The restriction to `U` of the second canonical map of Stacks 0AEX is invertible.** -/
theorem isIso_modulePullback_openImmersion_map_ambientOverlapMap (t : D.moduleGlueingComma)
    (ht : t.right.IsQuasicoherentOnSite) :
    IsIso ((modulePullback B S hS D.openImmersion).map (D.ambientOverlapMap.app t)) := by
  have h1 := isIso_map_whiskerRight_whiskerLeft_app
      (Comma.snd (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver))
      (modulePullbackAdjunction B S hS D.openImmersionOver).unit
      (modulePushforward B S hS D.ambientMorphism) (modulePullback B S hS D.openImmersion) t
      (D.isIso_modulePullback_openImmersion_map_pushforward_unit t.right ht)
  have h2 := ((Functor.isoWhiskerLeft
      (Comma.snd (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver) ⋙ modulePullback B S hS D.openImmersionOver)
      (modulePushforwardCompIso B S hS D.openImmersionOver D.ambientMorphism)).app t).isIso_hom
  exact isIso_map_comp_app D.ambientOverlapMap_eq (modulePullback B S hS D.openImmersion) t
    h1 h2

/-- **Stacks 0AF0, the map `γ`.**  For a glueing triple `(H, G, φ)` the map
`j^*Ker(j_*H ⊕ f_*G ⟶ (f ∘ j')_*G|_V) ⟶ H` is invertible.  The module of Stacks 0AEX is the
pullback of `j_*H` and `f_*G` over `(f ∘ j')_*G|_V`; restriction to `U` is exact and inverts the
second canonical map, so it inverts the first projection, and `j^*j_*H ⟶ H` is invertible
because `j` is an open immersion. -/
theorem isIso_glueingKernel_counit_left (t : D.moduleGlueingData) :
    IsIso ((modulePullback B S hS D.openImmersion).map (D.glueingKernelFst.app t.obj) ≫
      (modulePullbackAdjunction B S hS D.openImmersion).counit.app t.obj.left) := by
  have : PreservesFiniteLimits (modulePullback B S hS D.openImmersion) :=
    preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS _ D.isFlat_openImmersion
  have hP := (D.isPullback_glueingKernel_app t.obj).map (modulePullback B S hS D.openImmersion)
  have h := D.isIso_modulePullback_openImmersion_map_ambientOverlapMap t.obj t.property.2.2
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hP.isIso_fst_of_isIso h)
    (D.isIso_counit_openImmersion t.obj.left)

/-- **The map `γ`** of Stacks 0AF0: `j^*Ker(j_*H ⊕ f_*G ⟶ (f ∘ j')_*G|_V) ⟶ H`, the transpose
of the first projection, which is the left component of the counit of Stacks 0AEY. -/
abbrev glueingCounitLeft (t : D.moduleGlueingData) :=
  Adjunction.commaCounitLeft (modulePullbackAdjunction B S hS D.openImmersion) D.glueingKernelFst
    t.obj

/-- **The map `β`** of Stacks 0AF0: `f^*Ker(j_*H ⊕ f_*G ⟶ (f ∘ j')_*G|_V) ⟶ G`, the transpose
of the second projection, which is the right component of the counit of Stacks 0AEY. -/
abbrev glueingCounitRight (t : D.moduleGlueingData) :=
  Adjunction.commaCounitRight (modulePullbackAdjunction B S hS D.ambientMorphism)
    D.glueingKernelSnd t.obj

/-- The map `γ`, written as the transpose of the first projection. -/
theorem isIso_homEquiv_symm_glueingKernelFst (t : D.moduleGlueingData) :
    IsIso (D.glueingCounitLeft t) := by
  unfold glueingCounitLeft Adjunction.commaCounitLeft
  rw [Adjunction.homEquiv_counit (modulePullbackAdjunction B S hS D.openImmersion)
    (D.glueingKernelDiagram.obj t.obj) t.obj.left (D.glueingKernelFst.app t.obj)]
  exact D.isIso_glueingKernel_counit_left t

/-- **Stacks 0AF0, the map `β` over `V`.**  For a glueing triple `(H, G, φ)` the restriction to
`V` of `β : f^*Ker(j_*H ⊕ f_*G ⟶ (f ∘ j')_*G|_V) ⟶ G` is invertible: the counit of the adjunction
of Stacks 0AEY is a morphism of glueing triples, so the restriction of `β` to `V` is, up to the
overlap isomorphisms of the two triples, the pullback along `f|_V` of `γ`, which is invertible. -/
theorem isIso_openImmersionOver_map_homEquiv_symm_glueingKernelSnd (t : D.moduleGlueingData) :
    IsIso ((modulePullback B S hS D.openImmersionOver).map (D.glueingCounitRight t)) :=
  Adjunction.isIso_map_toCommaPullbackAdjunction_counit_right
    (modulePullbackAdjunction B S hS D.openImmersion)
    (modulePullbackAdjunction B S hS D.ambientMorphism)
    (modulePullbackAdjunction B S hS D.overlapRestriction)
    (modulePullbackAdjunction B S hS D.openImmersionOver)
    (modulePullbackAdjunction B S hS (D.openImmersionOver ≫ D.ambientMorphism))
    D.overlapPullbackCompIso
    (modulePullbackCompIso B S hS D.openImmersionOver D.ambientMorphism)
    (modulePushforwardCompIso B S hS D.overlapRestriction D.openImmersion)
    (eqToHom (congrArg (fun g : D.spaceV ⟶ D.spaceX => modulePushforward B S hS g)
      D.overlapRestriction_comp_openImmersion))
    (modulePushforwardCompIso B S hS D.openImmersionOver D.ambientMorphism)
    D.conjugateEquiv_overlapPullbackCompIso_inv
    D.conjugateEquiv_modulePullbackCompIso_overlap_inv
    D.overlapPullbackComparison D.overlapPullbackComparison_hom_app
    D.restrictionOverlapMap_eq D.ambientOverlapMap_eq D.isPullback_glueingKernel t.obj
    t.property.1 (D.isIso_homEquiv_symm_glueingKernelFst t)

/-- The adjunction of Stacks 0AEY is the restricted comma-pullback adjunction. -/
theorem glueingAdjunction_eq : D.glueingAdjunction = Adjunction.toCommaPullbackAdjunctionRestrict
    (modulePullbackAdjunction B S hS D.openImmersion)
    (modulePullbackAdjunction B S hS D.ambientMorphism)
    (modulePullbackAdjunction B S hS D.overlapRestriction)
    (modulePullbackAdjunction B S hS D.openImmersionOver)
    (modulePullbackAdjunction B S hS (D.openImmersionOver ≫ D.ambientMorphism))
    D.overlapPullbackCompIso
    (modulePullbackCompIso B S hS D.openImmersionOver D.ambientMorphism)
    (modulePushforwardCompIso B S hS D.overlapRestriction D.openImmersion)
    (eqToHom (congrArg (fun g : D.spaceV ⟶ D.spaceX => modulePushforward B S hS g)
      D.overlapRestriction_comp_openImmersion))
    (modulePushforwardCompIso B S hS D.openImmersionOver D.ambientMorphism)
    D.conjugateEquiv_overlapPullbackCompIso_inv
    D.conjugateEquiv_modulePullbackCompIso_overlap_inv
    D.overlapPullbackComparison D.overlapPullbackComparison_hom_app
    D.restrictionOverlapMap_eq D.ambientOverlapMap_eq D.isPullback_glueingKernel
    (show D.ambientInclusion.FullyFaithful from ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.fullyFaithfulι _)
    D.quasicoherentOverlapComparison D.quasicoherentOverlapComparison_eq rfl rfl := rfl

/-- **The counit of Stacks 0AEY is invertible at a glueing triple once `β` is.**  The map `γ` is
always invertible (`isIso_glueingKernel_counit_left`). -/
theorem isIso_glueingAdjunction_counit_app (t : D.moduleGlueingData)
    (hβ : IsIso (D.glueingCounitRight t)) :
    IsIso (D.glueingAdjunction.counit.app t) :=
  Adjunction.isIso_toCommaPullbackAdjunctionRestrict_counit_app
    (E₀ := QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2) (Q := D.moduleGlueingData)
    (Lq := D.glueingModulesFunctor)
    (Rq := D.glueingKernelFunctor)
    (modulePullbackAdjunction B S hS D.openImmersion)
    (modulePullbackAdjunction B S hS D.ambientMorphism)
    (modulePullbackAdjunction B S hS D.overlapRestriction)
    (modulePullbackAdjunction B S hS D.openImmersionOver)
    (modulePullbackAdjunction B S hS (D.openImmersionOver ≫ D.ambientMorphism))
    D.overlapPullbackCompIso
    (modulePullbackCompIso B S hS D.openImmersionOver D.ambientMorphism)
    (modulePushforwardCompIso B S hS D.overlapRestriction D.openImmersion)
    (eqToHom (congrArg (fun g : D.spaceV ⟶ D.spaceX => modulePushforward B S hS g)
      D.overlapRestriction_comp_openImmersion))
    (modulePushforwardCompIso B S hS D.openImmersionOver D.ambientMorphism)
    D.conjugateEquiv_overlapPullbackCompIso_inv
    D.conjugateEquiv_modulePullbackCompIso_overlap_inv
    D.overlapPullbackComparison D.overlapPullbackComparison_hom_app
    D.restrictionOverlapMap_eq D.ambientOverlapMap_eq D.isPullback_glueingKernel
    (show D.ambientInclusion.FullyFaithful from ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.fullyFaithfulι _)
    D.quasicoherentOverlapComparison D.quasicoherentOverlapComparison_eq rfl rfl
    D.glueingAdjunction D.glueingAdjunction_eq t t.obj rfl
    (D.isIso_homEquiv_symm_glueingKernelFst t) hβ

/-! ### The stalk checks -/

/-- **`β` on the fibre at a point of `V`.**  At a geometric point of `Y` coming from `V` the map
`β` is invertible on the fibre: its restriction to `V` is invertible, and the fibre of a
restriction along the open immersion `j'` is the fibre at the image point. -/
theorem isIso_fiber_glueingCounitRight_of_mem_V (t : D.moduleGlueingData)
    (v : GeometricPoint B S hS D.spaceV.1) :
    IsIso ((moduleFiber B S hS D.spaceY (geometricPointMap D.openImmersionOver.hom v)).map
      (D.glueingCounitRight t)) := by
  have h := D.isIso_openImmersionOver_map_homEquiv_symm_glueingKernelSnd t
  exact isIso_fiber_of_isIso_fiber_modulePullback D.openImmersionOver v
    (isFlatAt_of_isEtale _ (isEtale_of_isOpenImmersion B S hS
      D.isOpenImmersion_openImmersionOver) _) _ (@Functor.map_isIso _ _ _ _ _ _ _ _ h)

/-- **`β` is invertible once it is so on the fibres at the points of `f⁻¹(Z)`.**  The geometric
points of `Y` come from `V` or from `f⁻¹(Z)`, and at those from `V` the fibre of `β` is invertible
by `isIso_fiber_glueingCounitRight_of_mem_V`. -/
theorem isIso_glueingCounitRight_of_preimage (t : D.moduleGlueingData)
    (hZ : ∀ z : GeometricPoint B S hS (D.Z.preimage D.f).toFunctor,
      IsIso ((moduleFiber B S hS D.spaceY (geometricPointMap (D.Z.preimage D.f).ι z)).map
        (D.glueingCounitRight t))) :
    IsIso (D.glueingCounitRight t) := by
  refine isIso_of_isIso_fiber B S hS D.spaceY _ fun y => ?_
  rcases exists_geometricPoint_openComplement_or_closed B S hS D.algebraicSpace_Y _
      D.isClosedSubspace_preimage_Z D.V D.V_eq_openComplement_preimage y with ⟨v, rfl⟩ | ⟨z, rfl⟩
  · exact D.isIso_fiber_glueingCounitRight_of_mem_V t v
  · exact hZ z

/-- A geometric point of `X` lying in `Z` is the image of a geometric point of `f⁻¹(Z)` through
`Y`, since `f⁻¹(Z) ⟶ Z` is an isomorphism. -/
theorem exists_geometricPoint_preimage_of_Z (z : GeometricPoint B S hS D.Z.toFunctor) :
    ∃ y : GeometricPoint B S hS (D.Z.preimage D.f).toFunctor,
      geometricPointMap D.f (geometricPointMap (D.Z.preimage D.f).ι y) =
        geometricPointMap D.Z.ι z := by
  have := D.iso_over_Z
  refine ⟨geometricPointMap (inv (D.Z.fromPreimage D.f)) z, ?_⟩
  have h1 : (D.Z.preimage D.f).ι ≫ D.f = D.Z.fromPreimage D.f ≫ D.Z.ι :=
    (Subfunctor.fromPreimage_ι D.Z D.f).symm
  have h2 : geometricPointMap D.f (geometricPointMap (D.Z.preimage D.f).ι
      (geometricPointMap (inv (D.Z.fromPreimage D.f)) z)) =
      geometricPointMap (inv (D.Z.fromPreimage D.f) ≫ (D.Z.preimage D.f).ι ≫ D.f) z := rfl
  rw [h2, h1, IsIso.inv_hom_id_assoc]

/-- **The functor of Stacks 0AEW reflects isomorphisms.**  A map of quasi-coherent
`𝒪_X`-modules whose restriction to `U` and whose pullback to `Y` are invertible is invertible: at
a geometric point of `U` the fibre is the fibre of the restriction, and a geometric point of `Z`
is the image of a geometric point `ȳ` of `f⁻¹(Z)`, at which `f` is flat, so that the fibre of the
pullback is a faithfully flat base change of the fibre at the image. -/
instance reflectsIsomorphisms_glueingModulesFunctor :
    D.glueingModulesFunctor.ReflectsIsomorphisms where
  reflects {M N} φ hφ := by
    have h0 : IsIso ((ObjectProperty.ι _).map (D.glueingModulesFunctor.map φ)) :=
      Functor.map_isIso _ _
    have hl : IsIso ((modulePullback B S hS D.openImmersion).map φ.hom) :=
      (inferInstance : IsIso ((ObjectProperty.ι _).map (D.glueingModulesFunctor.map φ)).left)
    have hr : IsIso ((modulePullback B S hS D.ambientMorphism).map φ.hom) :=
      (inferInstance : IsIso ((ObjectProperty.ι _).map (D.glueingModulesFunctor.map φ)).right)
    have : IsIso φ.hom := by
      refine isIso_of_isIso_fiber B S hS D.spaceX _ fun x => ?_
      rcases exists_geometricPoint_openComplement_or_closed B S hS D.algebraicSpace_X D.Z
          D.closed_Z D.U rfl x with ⟨u, rfl⟩ | ⟨z, rfl⟩
      · exact isIso_fiber_of_isIso_fiber_modulePullback D.openImmersion u
          (isFlatAt_of_isEtale _ (isEtale_of_isOpenImmersion B S hS
            D.isOpenImmersion_openImmersion) _) _ (@Functor.map_isIso _ _ _ _ _ _ _ _ hl)
      · obtain ⟨y, hy⟩ := D.exists_geometricPoint_preimage_of_Z z
        rw [← hy]
        exact isIso_fiber_of_isIso_fiber_modulePullback D.ambientMorphism
          (geometricPointMap (D.Z.preimage D.f).ι y) (D.flat_at_preimage_Z y.image) _
          (@Functor.map_isIso _ _ _ _ _ _ _ _ hr)
    have : IsIso ((ObjectProperty.ι _).map φ) := this
    exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map φ

/-- **The reduction of Stacks 0AF0 to the fibres of `β` at the points of `f⁻¹(Z)`.**  If for
every glueing triple the map `β` is invertible on the fibre at every geometric point of `f⁻¹(Z)`,
then the unit and the counit of the adjunction of Stacks 0AEY are invertible.

The counit is invertible because `γ` always is and `β` is so on the fibres at the points of `V`;
the unit then is, because the left adjoint reflects isomorphisms and the triangle identity makes
its image of the unit the inverse of the counit. -/
theorem isIso_glueingAdjunction_unit_counit_of_fiber
    (hZ : ∀ (t : D.moduleGlueingData) (z : GeometricPoint B S hS (D.Z.preimage D.f).toFunctor),
      IsIso ((moduleFiber B S hS D.spaceY (geometricPointMap (D.Z.preimage D.f).ι z)).map
        (D.glueingCounitRight t))) :
    IsIso D.glueingAdjunction.unit ∧ IsIso D.glueingAdjunction.counit := by
  have hc : ∀ t, IsIso (D.glueingAdjunction.counit.app t) := fun t =>
    D.isIso_glueingAdjunction_counit_app t (D.isIso_glueingCounitRight_of_preimage t (hZ t))
  refine ⟨?_, NatIso.isIso_of_isIso_app _⟩
  have : ∀ M, IsIso (D.glueingAdjunction.unit.app M) :=
    Adjunction.isIso_unit_app_of_isIso_counit D.glueingAdjunction hc
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.Space.FormalGlueingSituation

end
