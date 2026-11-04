module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.Extension.Generators
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallyAffine
public import StacksFrontier.AlgebraicGeometry.Limits.SmallDominantIndex

/-!
# Descending closed immersions and immersions through an inverse limit

Let `X = lim X_i` be a directed inverse limit of quasi-compact and quasi-separated schemes over a
base `S`, with closed immersions as transition morphisms and with every `X_i ⟶ S` locally of
finite type. If `X ⟶ S` is a closed immersion then so is `X_i ⟶ S` for all sufficiently large
`i`; and if `X ⟶ S` is merely an immersion, and `S` is only quasi-separated, then `X_i ⟶ S` is an
immersion for all sufficiently large `i`.

## Main results

* `AlgebraicGeometry.eventually_isClosedImmersion`: a closed immersion of the limit descends to
  every sufficiently late stage.
* `AlgebraicGeometry.eventually_isImmersion`: an immersion of the limit descends to every
  sufficiently late stage.

## Implementation notes

The system over the base is recorded as a natural transformation to the constant diagram, and the
displayed equality identifies its restriction to the limiting cone with the given morphism to the
base. The source's hypothesis that the transition morphisms are affine is not repeated: every
closed immersion is affine.

The index preorder may live in any universe, but it is assumed small relative to the universe of
the schemes: the arguments run in a small model of the index and the conclusion is transported back
along the order isomorphism. A smallness assumption is not cosmetic: the limit of a diagram indexed
by a category larger than the universe of the schemes need not be computed by the filtered colimits
of coordinate rings that the proof uses, and for the affineness input (Tag 09ZM) the unrestricted
statement is false — see the module documentation of
`StacksFrontier/AlgebraicGeometry/Limits/EventuallyAffine.lean` for the counterexample. The source
indexes by a directed set, which is exactly this restriction.

Open neighbourhoods of the image descend by compactness: a point in the intersection of the
closed transition images determines a compatible cone out of its residue field, so an open whose
preimage in the limit is everything already has that property at a finite stage.

## References

* [Stacks Project, Tag 0A0N](https://stacks.math.columbia.edu/tag/0A0N)
* [Stacks Project, Tag 0GIH](https://stacks.math.columbia.edu/tag/0GIH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Filter Opposite

namespace AlgebraicGeometry

universe v u

variable {I : Type u}

/-! ### Reindexing helpers -/

/-- In a directed preorder, finitely many indices admit a common upper bound above a prescribed
one. -/
private theorem exists_ge_finset [Preorder I] [IsDirected I (· ≤ ·)]
    (s : Finset I) (i₀ : I) :
    ∃ i, i₀ ≤ i ∧ ∀ j ∈ s, j ≤ i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨i₀, le_rfl, by simp⟩
  | @insert a s _ ih =>
      obtain ⟨i, hi₀, his⟩ := ih
      obtain ⟨k, hak, hik⟩ := IsDirected.directed (r := (· ≤ ·)) a i
      refine ⟨k, hi₀.trans hik, fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      exacts [hak, (his j hj).trans hik]

/-- A `u`-small model of a directed preorder is directed. -/
private lemma isDirected_shrink {J : Type*} [Preorder J] [IsDirected J (· ≤ ·)] [Small.{u} J] :
    IsDirected (Shrink.{u} J) (· ≤ ·) := ⟨fun a b => by
  obtain ⟨k, ha, hb⟩ := IsDirected.directed (r := (· ≤ ·))
    ((orderIsoShrink.{u} J).symm a) ((orderIsoShrink.{u} J).symm b)
  exact ⟨orderIsoShrink.{u} J k, by simpa using (orderIsoShrink.{u} J).monotone ha,
    by simpa using (orderIsoShrink.{u} J).monotone hb⟩⟩

/-- A property holding at every sufficiently late index of a `u`-small model of a preorder holds
at every sufficiently late index of the preorder itself. -/
private lemma eventually_atTop_of_orderIsoShrink {J : Type v} [Preorder J]
    [IsDirected J (· ≤ ·)] [Small.{u} J] {P : J → Prop}
    (h : ∀ᶠ a in (atTop : Filter (Shrink.{u} J)), P ((orderIsoShrink.{u} J).symm a)) :
    ∀ᶠ j in atTop, P j := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · exact .of_forall isEmptyElim
  have : Nonempty (Shrink.{u} J) := (orderIsoShrink.{u} J).symm.toEquiv.nonempty
  have : IsDirected (Shrink.{u} J) (· ≤ ·) := isDirected_shrink
  obtain ⟨a₀, ha₀⟩ := Filter.eventually_atTop.1 h
  refine Filter.eventually_atTop.2 ⟨(orderIsoShrink.{u} J).symm a₀, fun j hj => ?_⟩
  have hle : a₀ ≤ orderIsoShrink.{u} J j := by
    simpa using (orderIsoShrink.{u} J).monotone hj
  simpa using ha₀ _ hle

/-- The transition morphisms of a system indexed by the opposite of a preorder are closed
immersions as soon as those attached to the relations `i ≤ j` are. -/
private lemma isClosedImmersion_map_of_le {J : Type*} [Preorder J] (D : Jᵒᵖ ⥤ Scheme.{u})
    [∀ ⦃i j : J⦄ (h : i ≤ j), IsClosedImmersion (D.map (homOfLE h).op)]
    {a b : Jᵒᵖ} (g : a ⟶ b) : IsClosedImmersion (D.map g) := by
  rw [Subsingleton.elim g (homOfLE (leOfHom g.unop)).op]
  infer_instance

/-- In a cofiltered category, finitely many objects admit a common source carrying also a morphism
to a prescribed object. -/
private theorem exists_common_source_finset [Category.{u} I] [IsCofiltered I]
    (s : Finset I) (i₀ : I) :
    ∃ k, Nonempty (k ⟶ i₀) ∧ ∀ j ∈ s, Nonempty (k ⟶ j) := by
  classical
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (insert i₀ s)
  exact ⟨k, hk (Finset.mem_insert_self _ _),
    fun j hj => hk (Finset.mem_insert_of_mem hj)⟩

/-- The component at `i` of the equality identifying the structure morphism induced on the limit
with the given morphism to the base. -/
private lemma cone_comp_app [Category.{u} I] {S : Scheme.{u}} {D : I ⥤ Scheme.{u}}
    {t : D ⟶ (Functor.const I).obj S} {c : Cone D} {f : c.pt ⟶ S}
    (hcomm : c.π ≫ t = (Functor.const I).map f) (i : I) :
    c.π.app i ≫ t.app i = f := by
  simpa using congrArg
    (fun n : (Functor.const I).obj c.pt ⟶ (Functor.const I).obj S => n.app i) hcomm

/-- Let `φ : B →+* C` be surjective and let `fk : R →+* C` agree with `φ` on the image of `R`. If
`φ` sends a family of generators of the `R`-algebra `B` into the image of `fk`, then `fk` is
surjective. -/
theorem _root_.RingHom.surjective_of_map_generators {R B C : Type*} [CommRing R] [CommRing B]
    [CommRing C] [Algebra R B] {σ : Type*} {x : σ → B}
    (hx : Function.Surjective (MvPolynomial.aeval (R := R) x)) (φ : B →+* C)
    (hφ : Function.Surjective φ) (fk : R →+* C) (hbase : φ.comp (algebraMap R B) = fk)
    (r : σ → R) (hgen : ∀ a, φ (x a) = fk (r a)) : Function.Surjective fk := by
  have hpoly : φ.comp (MvPolynomial.aeval (R := R) x).toRingHom =
      fk.comp (MvPolynomial.aeval (R := R) r).toRingHom :=
    MvPolynomial.ringHom_ext (fun s => by simpa using RingHom.congr_fun hbase s)
      (fun a => by simpa using hgen a)
  intro y
  obtain ⟨z, rfl⟩ := hφ y
  obtain ⟨p, rfl⟩ := hx z
  exact ⟨MvPolynomial.aeval r p, (RingHom.congr_fun hpoly p).symm⟩

section Stages

variable [Category.{u} I] [IsCofiltered I] {S : Scheme.{u}} (D : I ⥤ Scheme.{u})
  (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (f : c.pt ⟶ S)

/-- Finitely many equalities of global sections of a stage that hold on the limit already hold at
a common earlier stage. -/
private lemma exists_map_appTop_eq_of_isLimit [Quiver.IsThin I] (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] {i₀ : I} [CompactSpace (D.obj i₀)]
    {n : ℕ} (x y : Fin n → Γ(D.obj i₀, ⊤))
    (h : ∀ a, (c.π.app i₀).appTop (x a) = (c.π.app i₀).appTop (y a)) :
    ∃ (k : I) (α : k ⟶ i₀), ∀ a, (D.map α).appTop (x a) = (D.map α).appTop (y a) := by
  classical
  have hcpt : IsCompact (X := D.obj i₀) (⊤ : (D.obj i₀).Opens) := by
    simpa using isCompact_univ (X := D.obj i₀)
  choose j g hg using fun a => exists_app_map_eq_map_of_isLimit D c hc hcpt (x a) (y a) (h a)
  obtain ⟨k, ⟨α⟩, hjs⟩ := exists_common_source_finset (Finset.univ.image j) i₀
  refine ⟨k, α, fun a => ?_⟩
  obtain ⟨β⟩ := hjs (j a) (Finset.mem_image_of_mem _ (Finset.mem_univ a))
  have hroute : α = β ≫ g a := Subsingleton.elim _ _
  calc
    (D.map α).appTop (x a) = (D.map β).appTop ((D.map (g a)).appTop (x a)) := by
      rw [hroute, Functor.map_comp]
      rfl
    _ = (D.map β).appTop ((D.map (g a)).appTop (y a)) :=
      congrArg (D.map β).appTop (hg a)
    _ = (D.map α).appTop (y a) := by
      rw [hroute, Functor.map_comp]
      rfl

/-- The affine case of Tag 0A0N: over an affine base, a closed immersion of the limit is already a
closed immersion at some stage. The base ring surjects onto the coordinate ring of the limit, so
finitely many algebra generators of one stage agree there with elements coming from the base;
those agreements already hold at a finite stage, at which the coordinate ring is generated by the
image of the base. -/
private theorem exists_isClosedImmersion_app_of_isAffine
    [Quiver.IsThin I] [IsAffine S] (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] [∀ i, CompactSpace (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i)]
    (hcomm : c.π ≫ t = (Functor.const I).map f) [IsClosedImmersion f] :
    ∃ i, IsClosedImmersion (t.app i) := by
  have : ∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g) := fun g => inferInstance
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  let R := Γ(S, ⊤)
  let B := Γ(D.obj i₀, ⊤)
  let fi : R →+* B := (t.app i₀).appTop.hom
  have : IsAffine (((Functor.const I).obj S).obj i₀) := by
    simpa using (inferInstance : IsAffine S)
  have hfi : fi.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine
      (P := @LocallyOfFiniteType) (f := t.app i₀)).mp inferInstance
  let : Algebra R B := fi.toAlgebra
  have hfiAlg : (algebraMap R B).FiniteType := hfi
  obtain ⟨n, ⟨P⟩⟩ := Algebra.FiniteType.iff_exists_generators.mp
    ((RingHom.finiteType_algebraMap (A := R) (B := B)).mp hfiAlg)
  let x : Fin n → B := P.val
  choose r hr using fun a : Fin n =>
    f.app_surjective ⊤ (isAffineOpen_top S) ((c.π.app i₀).appTop (x a))
  have hring : (c.π.app i₀).appTop.hom.comp fi = f.appTop.hom := by
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      congrArg (fun g : c.pt ⟶ S => g.appTop.hom) (cone_comp_app hcomm i₀)
  obtain ⟨k, α, hk⟩ := exists_map_appTop_eq_of_isLimit D c hc x (fun a => fi (r a))
    fun a => (hr a).symm.trans (RingHom.congr_fun hring (r a)).symm
  let φ : B →+* Γ(D.obj k, ⊤) := (D.map α).appTop.hom
  let fk : R →+* Γ(D.obj k, ⊤) := (t.app k).appTop.hom
  have hbase : φ.comp fi = fk := by
    have hnat := congrArg (fun q : D.obj k ⟶ S => q.appTop.hom) (t.naturality α)
    simpa only [φ, fi, fk, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      Functor.const_obj_map, Scheme.Hom.id_appTop, CommRingCat.hom_id,
      RingHom.comp_id] using hnat
  have hgen (a : Fin n) : φ (x a) = fk (r a) := (hk a).trans (RingHom.congr_fun hbase (r a))
  have : IsAffine (((Functor.const I).obj S).obj k) := by
    simpa using (inferInstance : IsAffine S)
  exact ⟨k, IsClosedImmersion.of_surjective_of_isAffine _
    (RingHom.surjective_of_map_generators P.aeval_val_surjective φ
      ((D.map α).app_surjective ⊤ (isAffineOpen_top (D.obj i₀))) fk hbase r hgen)⟩

end Stages

section RestrictToAffine

variable [Category.{u} I] [IsCofiltered I] {S : Scheme.{u}} (D : I ⥤ Scheme.{u})
  (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (f : c.pt ⟶ S)

omit [IsCofiltered I] in
/-- The transition morphisms of the diagram of preimages of an open are closed immersions as soon
as the transition morphisms of the original diagram are. -/
private lemma isClosedImmersion_opensDiagram_map
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    {i : I} (V : (D.obj i).Opens) {j k : Over i} (a : j ⟶ k) :
    IsClosedImmersion ((opensDiagram D i V).map a) := by
  have : ∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g) := fun g => inferInstance
  let Uj : (D.obj j.left).Opens := D.map j.hom ⁻¹ᵁ V
  let Uk : (D.obj k.left).Opens := D.map k.hom ⁻¹ᵁ V
  have hV : Uj = (D.map a.left) ⁻¹ᵁ Uk := by
    dsimp [Uj, Uk]
    rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w a]
  let e : Uj.toScheme ≅ ((D.map a.left) ⁻¹ᵁ Uk).toScheme := Scheme.isoOfEq (D.obj j.left) hV
  have heq : (opensDiagram D i V).map a = e.hom ≫ (D.map a.left ∣_ Uk) := by
    apply (cancel_mono Uk.ι).1
    dsimp [opensDiagram]
    rw [Scheme.Hom.resLE_comp_ι, Category.assoc, AlgebraicGeometry.morphismRestrict_ι,
      ← Category.assoc, Scheme.isoOfEq_hom_ι]
  have : IsClosedImmersion (D.map a.left ∣_ Uk) := inferInstance
  have : IsClosedImmersion (e.hom ≫ (D.map a.left ∣_ Uk)) := inferInstance
  rw [heq]
  assumption

omit [IsCofiltered I] in
/-- If an open of a stage is affine, so is every member of the diagram of its preimages. -/
private lemma isAffine_opensDiagram_obj [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    {i : I} (V : (D.obj i).Opens) (hV : IsAffine V.toScheme) (j : Over i) :
    IsAffine ((opensDiagram D i V).obj j) := by
  let jtop : Over i := Over.mk (𝟙 i)
  let a : j ⟶ jtop := Over.homMk j.hom
  have : IsClosedImmersion ((opensDiagram D i V).map a) :=
    isClosedImmersion_opensDiagram_map D V a
  have htop : IsAffine ((opensDiagram D i V).obj jtop) := by
    simpa [jtop, opensDiagram] using hV
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine ((opensDiagram D i V).map a)).1

omit [IsCofiltered I] in
/-- A structure morphism from a quasi-compact stage to a quasi-separated base is quasi-compact. -/
private lemma quasiCompact_app [QuasiSeparatedSpace S] [∀ i, CompactSpace (D.obj i)] (i : I) :
    QuasiCompact (t.app i) := by
  have : QuasiSeparatedSpace (((Functor.const I).obj S).obj i) := by
    simpa using (inferInstance : QuasiSeparatedSpace S)
  exact AlgebraicGeometry.quasiCompact_of_compactSpace (t.app i)

omit [IsCofiltered I] in
/-- Pulling back the preimage of an open of the base along a transition morphism gives the
preimage of that open at the earlier stage. -/
private lemma map_preimage_app_preimage (U : S.Opens) {i : I} (j : Over i) :
    D.map j.hom ⁻¹ᵁ (t.app i ⁻¹ᵁ U) = t.app j.left ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage]
  congr 1
  simp [t.naturality j.hom]

omit [IsCofiltered I] in
/-- The structure morphisms of the stages over `i`, restricted over an open `U` of the base, as a
transformation to the constant diagram on `U`. -/
private noncomputable def opensDiagramToOpen (i : I) (U : S.Opens) :
    opensDiagram D i (t.app i ⁻¹ᵁ U) ⟶ (Functor.const (Over i)).obj U.toScheme where
  app j := (t.app j.left).resLE U (D.map j.hom ⁻¹ᵁ (t.app i ⁻¹ᵁ U))
    (map_preimage_app_preimage D t U j).le
  naturality := by
    intro j k a
    apply (cancel_mono U.ι).1
    dsimp [opensDiagram]
    simp [Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_resLE, t.naturality]

omit [IsCofiltered I] in
private lemma opensDiagramToOpen_app (i : I) (U : S.Opens) (j : Over i) :
    (opensDiagramToOpen D t i U).app j =
      (Scheme.isoOfEq (D.obj j.left) (map_preimage_app_preimage D t U j)).hom ≫
        (t.app j.left ∣_ U) := by
  dsimp [opensDiagramToOpen, Scheme.Hom.resLE]
  rfl

omit [IsCofiltered I] in
/-- At the initial object over `i`, the restricted structure morphism of the cone of preimages is
the restriction of the morphism from the limit. -/
private lemma opensCone_π_comp_opensDiagramToOpen (hcomm : c.π ≫ t = (Functor.const I).map f)
    (i : I) (U : S.Opens) (h : c.π.app i ⁻¹ᵁ (t.app i ⁻¹ᵁ U) = f ⁻¹ᵁ U) :
    (opensCone D c i (t.app i ⁻¹ᵁ U)).π.app (Over.mk (𝟙 i)) ≫
        (opensDiagramToOpen D t i U).app (Over.mk (𝟙 i)) =
      (Scheme.isoOfEq c.pt h).hom ≫ (f ∣_ U) := by
  apply (cancel_mono U.ι).1
  have h1 : (opensDiagramToOpen D t i U).app (Over.mk (𝟙 i)) ≫ U.ι =
      (D.map (𝟙 i) ⁻¹ᵁ (t.app i ⁻¹ᵁ U)).ι ≫ t.app i :=
    Scheme.Hom.resLE_comp_ι (t.app i) _
  have h2 : (opensCone D c i (t.app i ⁻¹ᵁ U)).π.app (Over.mk (𝟙 i)) ≫
      (D.map (𝟙 i) ⁻¹ᵁ (t.app i ⁻¹ᵁ U)).ι = (c.π.app i ⁻¹ᵁ (t.app i ⁻¹ᵁ U)).ι ≫ c.π.app i :=
    Scheme.Hom.resLE_comp_ι (c.π.app i) _
  have hL : ((opensCone D c i (t.app i ⁻¹ᵁ U)).π.app (Over.mk (𝟙 i)) ≫
      (opensDiagramToOpen D t i U).app (Over.mk (𝟙 i))) ≫ U.ι =
        (c.π.app i ⁻¹ᵁ (t.app i ⁻¹ᵁ U)).ι ≫ f := by
    refine (Category.assoc _ _ _).trans ?_
    rw [h1]
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [h2]
    exact (Category.assoc _ _ _).trans (congrArg _ (cone_comp_app hcomm i))
  have hR : ((Scheme.isoOfEq c.pt h).hom ≫ (f ∣_ U)) ≫ U.ι =
      (c.π.app i ⁻¹ᵁ (t.app i ⁻¹ᵁ U)).ι ≫ f := by
    rw [Category.assoc, AlgebraicGeometry.morphismRestrict_ι, ← Category.assoc]
    exact congrArg (· ≫ f) (Scheme.isoOfEq_hom_ι c.pt h)
  exact hL.trans hR.symm

/-- Tag 0A0N over an affine open `U` of the base, once the preimage of `U` at some stage is
affine: from there on the diagram of preimages is affine and the affine case applies. -/
private theorem exists_isClosedImmersion_morphismRestrict_of_isAffine [Quiver.IsThin I]
    (hc : IsLimit c) [QuasiSeparatedSpace S] [∀ i, CompactSpace (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i)]
    (hcomm : c.π ≫ t = (Functor.const I).map f) [IsClosedImmersion f]
    (U : S.Opens) (hU : IsAffineOpen U) (i₁ : I) (hV : IsAffine (t.app i₁ ⁻¹ᵁ U).toScheme) :
    ∃ i, IsClosedImmersion (t.app i ∣_ U) := by
  have : ∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g) := fun g => inferInstance
  have : IsAffine U := hU
  set V₁ : (D.obj i₁).Opens := t.app i₁ ⁻¹ᵁ U
  have hE₁aff := isAffine_opensDiagram_obj D V₁ hV
  have hV₁cpt : IsCompact (V₁ : Set (D.obj i₁)) :=
    (quasiCompact_app D t i₁).isCompact_preimage _ U.2 hU.isCompact
  have hE₁compact (j : Over i₁) : CompactSpace ((opensDiagram D i₁ V₁).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ V₁.2 hV₁cpt)
  let T₁ := opensDiagramToOpen D t i₁ U
  let ej (j : Over i₁) : (opensDiagram D i₁ V₁).obj j ≅ (t.app j.left ⁻¹ᵁ U).toScheme :=
    Scheme.isoOfEq (D.obj j.left) (map_preimage_app_preimage D t U j)
  have hTj (j : Over i₁) : T₁.app j = (ej j).hom ≫ (t.app j.left ∣_ U) :=
    opensDiagramToOpen_app D t i₁ U j
  have hopenLim₁ : c.π.app i₁ ⁻¹ᵁ V₁ = f ⁻¹ᵁ U := by
    dsimp [V₁]
    rw [← Scheme.Hom.comp_preimage, cone_comp_app hcomm i₁]
  let jtop : Over i₁ := Over.mk (𝟙 i₁)
  let f₁ : (opensCone D c i₁ V₁).pt ⟶ U.toScheme :=
    (opensCone D c i₁ V₁).π.app jtop ≫ T₁.app jtop
  have hcomm₁ : (opensCone D c i₁ V₁).π ≫ T₁ = (Functor.const (Over i₁)).map f₁ := by
    ext j
    let a : j ⟶ jtop := Over.homMk j.hom
    have hnat : (opensDiagram D i₁ V₁).map a ≫ T₁.app jtop = T₁.app j := by
      simpa using T₁.naturality a
    calc
      (opensCone D c i₁ V₁).π.app j ≫ T₁.app j =
          ((opensCone D c i₁ V₁).π.app j ≫ (opensDiagram D i₁ V₁).map a) ≫ T₁.app jtop := by
        rw [Category.assoc, hnat]
      _ = f₁ := congrArg (fun g => g ≫ T₁.app jtop) ((opensCone D c i₁ V₁).w a)
  let e₁ : (opensCone D c i₁ V₁).pt ≅ (f ⁻¹ᵁ U).toScheme := Scheme.isoOfEq c.pt hopenLim₁
  have hf₁eq : f₁ = e₁.hom ≫ (f ∣_ U) :=
    opensCone_π_comp_opensDiagramToOpen D t c f hcomm i₁ U hopenLim₁
  have hf₁ : IsClosedImmersion f₁ := by
    rw [hf₁eq]
    infer_instance
  have : ∀ j, IsAffine ((opensDiagram D i₁ V₁).obj j) := hE₁aff
  have : ∀ j, CompactSpace ((opensDiagram D i₁ V₁).obj j) := hE₁compact
  have : ∀ {j k : Over i₁} (a : j ⟶ k), IsClosedImmersion ((opensDiagram D i₁ V₁).map a) :=
    fun a => isClosedImmersion_opensDiagram_map D V₁ a
  have : ∀ j, LocallyOfFiniteType (T₁.app j) := by
    intro j
    rw [hTj j]
    infer_instance
  obtain ⟨j, hj⟩ := exists_isClosedImmersion_app_of_isAffine (opensDiagram D i₁ V₁) T₁
    (opensCone D c i₁ V₁) f₁ (isLimitOpensCone D c hc i₁ V₁) hcomm₁
  refine ⟨j.left, ?_⟩
  rw [hTj j] at hj
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := @IsClosedImmersion) (ej j).hom (t.app j.left ∣_ U)).mp hj

/-- Tag 0A0N restricted to an affine open of the base: the structure morphism of some stage,
restricted over that open, is a closed immersion. The diagram of preimages has an affine stage by
Tag 01Z6, and from there the affine case applies. -/
private theorem exists_isClosedImmersion_morphismRestrict [Quiver.IsThin I] (hc : IsLimit c)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i)]
    (hcomm : c.π ≫ t = (Functor.const I).map f) [IsClosedImmersion f]
    (U : S.Opens) (hU : IsAffineOpen U) :
    ∃ i, IsClosedImmersion (t.app i ∣_ U) := by
  have : ∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g) := fun g => inferInstance
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  set V₀ : (D.obj i₀).Opens := t.app i₀ ⁻¹ᵁ U
  have hpt₀ : (opensCone D c i₀ V₀).pt = (f ⁻¹ᵁ U).toScheme := by
    apply congrArg Scheme.Opens.toScheme
    simp [V₀, ← Scheme.Hom.comp_preimage, cone_comp_app hcomm i₀]
  have : IsAffine U := hU
  have : IsAffine (opensCone D c i₀ V₀).pt := by
    rw [hpt₀]
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine (f ∣_ U)).1
  have hV₀cpt : IsCompact (V₀ : Set (D.obj i₀)) :=
    (quasiCompact_app D t i₀).isCompact_preimage _ U.2 hU.isCompact
  have hE₀compact (j : Over i₀) : CompactSpace ((opensDiagram D i₀ V₀).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ V₀.2 hV₀cpt)
  have hE₀qs (j : Over i₀) : QuasiSeparatedSpace ((opensDiagram D i₀ V₀).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map j.hom ⁻¹ᵁ V₀).2).mp
      (.of_quasiSeparatedSpace _)
  obtain ⟨j₁, hj₁⟩ := Scheme.exists_isAffine_of_isLimit (opensDiagram D i₀ V₀)
    (opensCone D c i₀ V₀) (isLimitOpensCone D c hc i₀ V₀)
  refine exists_isClosedImmersion_morphismRestrict_of_isAffine D t c f hc hcomm U hU j₁.left ?_
  rw [← map_preimage_app_preimage D t U j₁]
  exact hj₁

end RestrictToAffine

/-! ### Tag 0A0N -/

/-- Tag 0A0N for an index preorder that already lives in the universe of the schemes: the closed
immersion of the limit descends to every sufficiently late stage. The general statement is
`AlgebraicGeometry.eventually_isClosedImmersion`, obtained from this one by transport along an
order isomorphism onto a small model of the index. -/
private lemma eventually_isClosedImmersion_of_indexSmall
    [Preorder I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const Iᵒᵖ).obj S) (c : Cone D) (hc : IsLimit c)
    (f : c.pt ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [∀ i, CompactSpace (D.obj (op i))]
    [∀ i, QuasiSeparatedSpace (D.obj (op i))]
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsClosedImmersion (D.map (homOfLE h).op)]
    [∀ i, LocallyOfFiniteType (t.app (op i))]
    (hcomm : c.π ≫ t = (Functor.const Iᵒᵖ).map f)
    [IsClosedImmersion f] :
    ∀ᶠ i in atTop, IsClosedImmersion (t.app (op i)) := by
  classical
  rcases isEmpty_or_nonempty I with hI | hI
  · exact .of_forall isEmptyElim
  have hclosed {a b : Iᵒᵖ} (g : a ⟶ b) : IsClosedImmersion (D.map g) :=
    isClosedImmersion_map_of_le D g
  have : ∀ i, CompactSpace (D.obj i) := fun i => ‹∀ i, CompactSpace (D.obj (op i))› i.unop
  have : ∀ i, QuasiSeparatedSpace (D.obj i) :=
    fun i => ‹∀ i, QuasiSeparatedSpace (D.obj (op i))› i.unop
  have : ∀ i, LocallyOfFiniteType (t.app i) :=
    fun i => ‹∀ i, LocallyOfFiniteType (t.app (op i))› i.unop
  let 𝒰 := S.affineCover.finiteSubcover
  have htop : ⨆ a : 𝒰.I₀, (𝒰.f a).opensRange = ⊤ := 𝒰.iSup_opensRange
  choose jop hjop using fun a : 𝒰.I₀ =>
    exists_isClosedImmersion_morphismRestrict D t c f hc hcomm (𝒰.f a).opensRange
      (isAffineOpen_opensRange (𝒰.f a))
  let j (a : 𝒰.I₀) : I := (jop a).unop
  let s : Finset I := Finset.univ.image j
  obtain ⟨k, _, hsk⟩ := exists_ge_finset s (Classical.choice ‹Nonempty I›)
  have hk' (a : 𝒰.I₀) : j a ≤ k := hsk (j a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
  have hrestr (a : 𝒰.I₀) : IsClosedImmersion (t.app (op k) ∣_ (𝒰.f a).opensRange) := by
    let g : op k ⟶ op (j a) := (homOfLE (hk' a)).op
    let V : (D.obj (op (j a))).Opens := t.app (op (j a)) ⁻¹ᵁ (𝒰.f a).opensRange
    have hcomp : D.map g ≫ t.app (op (j a)) = t.app (op k) := by
      simp
    have hpre : D.map g ⁻¹ᵁ V = (t.app (op k)) ⁻¹ᵁ (𝒰.f a).opensRange := by
      dsimp [V]
      rw [← Scheme.Hom.comp_preimage, hcomp]
    let e : (D.map g ⁻¹ᵁ V).toScheme ≅
        ((t.app (op k)) ⁻¹ᵁ (𝒰.f a).opensRange).toScheme := Scheme.isoOfEq (D.obj (op k)) hpre
    have hfactor : e.hom ≫ (t.app (op k) ∣_ (𝒰.f a).opensRange) =
        (D.map g ∣_ V) ≫ (t.app (op (j a)) ∣_ (𝒰.f a).opensRange) := by
      apply (cancel_mono (𝒰.f a).opensRange.ι).1
      simp only [e, Scheme.isoOfEq_hom_ι_assoc, AlgebraicGeometry.morphismRestrict_ι,
        Category.assoc]
      rw [← Category.assoc, AlgebraicGeometry.morphismRestrict_ι, Category.assoc, hcomp]
    have hfactorClosed :
        IsClosedImmersion (e.hom ≫ (t.app (op k) ∣_ (𝒰.f a).opensRange)) := by
      rw [hfactor]
      have : IsClosedImmersion (D.map g) := hclosed g
      have : IsClosedImmersion (t.app (op (j a)) ∣_ (𝒰.f a).opensRange) := hjop a
      infer_instance
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @IsClosedImmersion) (f := e.hom)
      (g := t.app (op k) ∣_ (𝒰.f a).opensRange)).mp hfactorClosed
  have hclosedk : IsClosedImmersion (t.app (op k)) :=
    IsZariskiLocalAtTarget.of_iSup_eq_top
      (fun a : 𝒰.I₀ => (𝒰.f a).opensRange) htop hrestr
  refine Filter.eventually_atTop.2 ⟨k, fun i hi => ?_⟩
  rw [← show D.map (homOfLE hi).op ≫ t.app (op k) = t.app (op i) by simp]
  infer_instance

/-- A property of the structure morphisms that holds eventually for every system indexed by a
`u`-small model of the index also holds eventually for a system indexed by the index itself. -/
private lemma eventually_atTop_of_indexSmall {I : Type v} [Preorder I]
    [IsDirected I (· ≤ ·)] [Small.{u} I]
    {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const Iᵒᵖ).obj S) (c : Cone D) (hc : IsLimit c)
    (f : c.pt ⟶ S) (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → Prop) (hf : P f)
    [∀ i, CompactSpace (D.obj (op i))]
    [∀ i, QuasiSeparatedSpace (D.obj (op i))]
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsClosedImmersion (D.map (homOfLE h).op)]
    [∀ i, LocallyOfFiniteType (t.app (op i))]
    (hcomm : c.π ≫ t = (Functor.const Iᵒᵖ).map f)
    (H : ∀ (D' : (Shrink.{u} I)ᵒᵖ ⥤ Scheme.{u})
      (t' : D' ⟶ (Functor.const (Shrink.{u} I)ᵒᵖ).obj S)
      (c' : Cone D') (_ : IsLimit c')
      [∀ a, CompactSpace (D'.obj (op a))] [∀ a, QuasiSeparatedSpace (D'.obj (op a))]
      [∀ ⦃a b : Shrink.{u} I⦄ (h : a ≤ b), IsClosedImmersion (D'.map (homOfLE h).op)]
      [∀ a, LocallyOfFiniteType (t'.app (op a))] [IsDirected (Shrink.{u} I) (· ≤ ·)]
      (f' : c'.pt ⟶ S), P f' → c'.π ≫ t' = (Functor.const (Shrink.{u} I)ᵒᵖ).map f' →
        ∀ᶠ a in atTop, P (t'.app (op a))) :
    ∀ᶠ i in atTop, P (t.app (op i)) := by
  classical
  let e := orderIsoShrink.{u} I
  have : IsDirected (Shrink.{u} I) (· ≤ ·) := isDirected_shrink
  let E := e.symm.equivalence.op
  let D' : (Shrink.{u} I)ᵒᵖ ⥤ Scheme.{u} := E.functor ⋙ D
  let t' : D' ⟶ (Functor.const (Shrink.{u} I)ᵒᵖ).obj S := Functor.whiskerLeft E.functor t
  let c' : Cone D' := c.whisker E.functor
  have hc' : IsLimit c' := hc.whiskerEquivalence E
  have : ∀ a : Shrink.{u} I, CompactSpace (D'.obj (op a)) :=
    fun a => ‹∀ i, CompactSpace (D.obj (op i))› (e.symm a)
  have : ∀ a : Shrink.{u} I, QuasiSeparatedSpace (D'.obj (op a)) :=
    fun a => ‹∀ i, QuasiSeparatedSpace (D.obj (op i))› (e.symm a)
  have : ∀ ⦃a b : Shrink.{u} I⦄ (h : a ≤ b), IsClosedImmersion (D'.map (homOfLE h).op) :=
    fun _ _ h => isClosedImmersion_map_of_le D (E.functor.map (homOfLE h).op)
  have : ∀ a : Shrink.{u} I, LocallyOfFiniteType (t'.app (op a)) :=
    fun a => ‹∀ i, LocallyOfFiniteType (t.app (op i))› (e.symm a)
  exact eventually_atTop_of_orderIsoShrink
    (H D' t' c' hc' f hf (by
      ext a
      exact (show c.π.app (E.functor.obj a) ≫ t.app (E.functor.obj a) = f by
        simpa using congrArg (fun n => n.app (E.functor.obj a)) hcomm)))

/-- In a directed inverse system of quasi-compact and quasi-separated schemes whose transition
morphisms are closed immersions, if all the structure morphisms to a quasi-compact and
quasi-separated base are locally of finite type and the morphism induced on the limit is a closed
immersion, then the structure morphisms are closed immersions for all sufficiently large indices.

This is the `Filter.atTop` form, over a directed preorder, of
`AlgebraicGeometry.eventually_isClosedImmersion_app_of_isLimit_of_initiallySmall`, which states
the same descent for a cofiltered index category. -/
lemma eventually_isClosedImmersion {I : Type v} [Preorder I]
    [IsDirected I (· ≤ ·)] [Small.{u} I]
    {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const Iᵒᵖ).obj S) (c : Cone D) (hc : IsLimit c)
    (f : c.pt ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [∀ i, CompactSpace (D.obj (op i))]
    [∀ i, QuasiSeparatedSpace (D.obj (op i))]
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsClosedImmersion (D.map (homOfLE h).op)]
    [∀ i, LocallyOfFiniteType (t.app (op i))]
    (hcomm : c.π ≫ t = (Functor.const Iᵒᵖ).map f)
    [IsClosedImmersion f] :
    ∀ᶠ i in atTop, IsClosedImmersion (t.app (op i)) := by
  exact eventually_atTop_of_indexSmall D t c hc f (@IsClosedImmersion) inferInstance hcomm
      @fun D' t' c' hc' _ _ _ _ _ f' hf' hcomm' => by
        have := hf'
        exact eventually_isClosedImmersion_of_indexSmall D' t' c' hc' f' hcomm'

/-! ### Tag 0GIH -/

/-- An immersion with quasi-compact source factors as a closed immersion into a quasi-compact open
of the target. -/
private lemma exists_isClosedImmersion_lift_of_isImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace X] [IsImmersion f] :
    ∃ U : S.Opens, IsCompact (U : Set S) ∧
      ∃ g : X ⟶ U.toScheme, IsClosedImmersion g ∧ g ≫ U.ι = f := by
  obtain ⟨Z, g, k, hg, hk, hgf⟩ := IsImmersion.isImmersion_iff_exists.mp ‹IsImmersion f›
  have hRange : Set.range f ⊆ k.opensRange := by
    rw [← hgf]
    rintro _ ⟨x, rfl⟩
    exact ⟨g x, rfl⟩
  obtain ⟨U, hUcompact, hUk, hU⟩ := exists_compactOpen_covering_range f hRange
  let fU := IsOpenImmersion.lift U.ι f (by simpa using hU)
  have hfU : fU ≫ U.ι = f := IsOpenImmersion.lift_fac ..
  let j := IsOpenImmersion.lift k U.ι (by rwa [Scheme.Opens.range_ι])
  have hj : j ≫ k = U.ι := IsOpenImmersion.lift_fac ..
  have : IsOpenImmersion (j ≫ k) := by
    rw [hj]
    infer_instance
  have : IsOpenImmersion j := .of_comp j k
  have hfUg : fU ≫ j = g := by
    apply (cancel_mono k).1
    rw [Category.assoc, hj, hfU, hgf]
  have : IsClosedImmersion (fU ≫ j) := hfUg ▸ hg
  exact ⟨U, hUcompact, fU, .of_comp fU j, hfU⟩

/-- A morphism whose preimage of `U` is everything, viewed as a morphism into `U`. -/
private noncomputable abbrev liftToOpen {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Opens) (h : f ⁻¹ᵁ U = ⊤) : X ⟶ U.toScheme :=
  X.topIso.inv ≫ f.resLE U ⊤ h.ge

private lemma liftToOpen_comp {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Opens) (h : f ⁻¹ᵁ U = ⊤) : liftToOpen f U h ≫ U.ι = f := by
  rw [liftToOpen, Category.assoc, Scheme.Hom.resLE_comp_ι]
  simp

private lemma liftToOpen_naturality {X Y S : Scheme.{u}} (g : X ⟶ Y)
    (fX : X ⟶ S) (fY : Y ⟶ S) (U : S.Opens)
    (hX : fX ⁻¹ᵁ U = ⊤) (hY : fY ⁻¹ᵁ U = ⊤) (hcomp : g ≫ fY = fX) :
    g ≫ liftToOpen fY U hY = liftToOpen fX U hX := by
  apply (cancel_mono U.ι).1
  rw [Category.assoc, liftToOpen_comp, liftToOpen_comp, hcomp]

/-- The tail of a preorder above a given element. -/
public abbrev LimitTail (P : Type u) [Preorder P] (i : P) := {j : P // i ≤ j}

/-- The opposite of a tail of a preorder is the category of objects over the corresponding
object. -/
public noncomputable def limitTailOverEquiv {P : Type u} [Preorder P] (i : P) :
    (LimitTail P i)ᵒᵖ ≌ Over (op i) where
  functor :=
    { obj := fun j => Over.mk ((homOfLE j.unop.2).op)
      map := fun {j k} a => Over.homMk ((homOfLE (leOfHom a.unop)).op)
      map_id := by
        intro j
        apply Over.OverMorphism.ext
        apply Subsingleton.elim
      map_comp := by
        intro a b d p q
        apply Over.OverMorphism.ext
        apply Subsingleton.elim }
  inverse :=
    { obj := fun A => op ⟨A.left.unop, leOfHom A.hom.unop⟩
      map := fun {A B} a => (homOfLE (leOfHom a.left.unop)).op
      map_id := by
        intro A
        apply Subsingleton.elim
      map_comp := by
        intro A B C p q
        apply Subsingleton.elim }
  unitIso := NatIso.ofComponents (fun j => eqToIso (by cases j; rfl))
    (by intro a b p; subsingleton)
  counitIso := NatIso.ofComponents
    (fun A => Over.isoMk (Iso.refl _) (by apply Subsingleton.elim))
    (by intro A B p; rfl)

/-- Under the hypotheses of Tag 0GIH, the immersion of the limit factors as a closed immersion
through a quasi-compact open of the base which contains the image of every sufficiently late
stage. -/
private lemma exists_isClosedImmersion_lift_preimage_eq_top
    [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const Iᵒᵖ).obj S) (c : Cone D) (hc : IsLimit c)
    (f : c.pt ⟶ S)
    [∀ i, CompactSpace (D.obj (op i))]
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsClosedImmersion (D.map (homOfLE h).op)]
    (hcomm : c.π ≫ t = (Functor.const Iᵒᵖ).map f)
    [IsImmersion f] :
    ∃ U : S.Opens, IsCompact (U : Set S) ∧ ∃ fU : c.pt ⟶ U.toScheme, IsClosedImmersion fU ∧
      fU ≫ U.ι = f ∧ ∃ i₁ : I, ∀ (i : Iᵒᵖ) (_ : i ⟶ op i₁), t.app i ⁻¹ᵁ U = ⊤ := by
  have hclosed {a b : Iᵒᵖ} (g : a ⟶ b) : IsClosedImmersion (D.map g) :=
    isClosedImmersion_map_of_le D g
  have : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom (D.map g) := fun g => inferInstance
  have : ∀ i : Iᵒᵖ, CompactSpace (D.obj i) :=
    fun i => ‹∀ i, CompactSpace (D.obj (op i))› i.unop
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  obtain ⟨U, hUcompact, fU, hfUclosed, hfU⟩ := exists_isClosedImmersion_lift_of_isImmersion f
  have hRangeU : Set.range f ⊆ U := by
    rw [← hfU]
    rintro _ ⟨x, rfl⟩
    exact (fU x).property
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hV : c.π.app (op i₀) ⁻¹ᵁ (t.app (op i₀) ⁻¹ᵁ U) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, cone_comp_app hcomm]
    apply SetLike.coe_injective
    ext x
    exact ⟨fun _ => trivial, fun _ => hRangeU ⟨x, rfl⟩⟩
  obtain ⟨⟨i₁⟩, q, hq⟩ := exists_map_eq_top D c hc (t.app (op i₀) ⁻¹ᵁ U) hV
  have hpull {i j : Iᵒᵖ} (a : i ⟶ j) (h : D.map a ⁻¹ᵁ (t.app j ⁻¹ᵁ U) = ⊤) :
      t.app i ⁻¹ᵁ U = ⊤ := by
    rwa [← Scheme.Hom.comp_preimage, (t.naturality a).trans (Category.comp_id _)] at h
  have hi₁ : t.app (op i₁) ⁻¹ᵁ U = ⊤ := hpull q hq
  exact ⟨U, hUcompact, fU, hfUclosed, hfU, i₁, fun i a => hpull a (by simp [hi₁])⟩

/-- Tag 0GIH for a system all of whose stages map into an open `U` of the base through which the
limit factors as a closed immersion: the stages, viewed over `U`, are eventually closed
immersions. -/
private lemma eventually_isImmersion_of_preimage_eq_top
    [Preorder I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const Iᵒᵖ).obj S) (c : Cone D) (hc : IsLimit c)
    (f : c.pt ⟶ S)
    [∀ i, CompactSpace (D.obj (op i))]
    [∀ i, QuasiSeparatedSpace (D.obj (op i))]
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsClosedImmersion (D.map (homOfLE h).op)]
    [∀ i, LocallyOfFiniteType (t.app (op i))]
    (hcomm : c.π ≫ t = (Functor.const Iᵒᵖ).map f)
    (U : S.Opens) [CompactSpace U.toScheme] [QuasiSeparatedSpace U.toScheme]
    (fU : c.pt ⟶ U.toScheme) [IsClosedImmersion fU] (hfU : fU ≫ U.ι = f)
    (hU : ∀ i, t.app i ⁻¹ᵁ U = ⊤) :
    ∀ᶠ i in atTop, IsImmersion (t.app (op i)) := by
  let tU : D ⟶ (Functor.const Iᵒᵖ).obj U.toScheme :=
    { app i := liftToOpen (t.app i) U (hU i)
      naturality := by
        intro i j φ
        exact liftToOpen_naturality (D.map φ) (t.app i) (t.app j) U (hU i) (hU j)
          ((t.naturality φ).trans (Category.comp_id _)) }
  have hcommU : c.π ≫ tU = (Functor.const Iᵒᵖ).map fU := by
    ext i
    apply (cancel_mono U.ι).1
    calc
      (c.π.app i ≫ tU.app i) ≫ U.ι = c.π.app i ≫ t.app i := by
        rw [Category.assoc]
        exact congrArg (fun g => c.π.app i ≫ g) (liftToOpen_comp (t.app i) U (hU i))
      _ = f := cone_comp_app hcomm i
      _ = fU ≫ U.ι := hfU.symm
  have : ∀ i, LocallyOfFiniteType (tU.app (op i)) := by
    intro i
    dsimp [tU, liftToOpen]
    infer_instance
  filter_upwards [eventually_isClosedImmersion_of_indexSmall D tU c hc fU hcommU] with i hi
  have hfactor : tU.app (op i) ≫ U.ι = t.app (op i) := liftToOpen_comp (t.app (op i)) U (hU _)
  rw [← hfactor]
  exact IsImmersion.isImmersion_iff_exists.mpr ⟨_, _, _, hi, inferInstance, rfl⟩

/-- Tag 0GIH for an index preorder that already lives in the universe of the schemes: the immersion
of the limit descends to every sufficiently late stage. The general statement is
`AlgebraicGeometry.eventually_isImmersion`, obtained from this one by transport along an order
isomorphism onto a small model of the index. -/
private lemma eventually_isImmersion_of_indexSmall
    [Preorder I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const Iᵒᵖ).obj S) (c : Cone D) (hc : IsLimit c)
    (f : c.pt ⟶ S)
    [QuasiSeparatedSpace S]
    [∀ i, CompactSpace (D.obj (op i))]
    [∀ i, QuasiSeparatedSpace (D.obj (op i))]
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsClosedImmersion (D.map (homOfLE h).op)]
    [∀ i, LocallyOfFiniteType (t.app (op i))]
    (hcomm : c.π ≫ t = (Functor.const Iᵒᵖ).map f)
    [IsImmersion f] :
    ∀ᶠ i in atTop, IsImmersion (t.app (op i)) := by
  rcases isEmpty_or_nonempty I with hI | hI
  · exact .of_forall isEmptyElim
  obtain ⟨U, hUcompact, fU, hfUclosed, hfU, i₁, hstageTop⟩ :=
    exists_isClosedImmersion_lift_preimage_eq_top D t c hc f hcomm
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hUcompact
  have : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_quasiSeparated U.ι
  have hclosed {a b : Iᵒᵖ} (g : a ⟶ b) : IsClosedImmersion (D.map g) :=
    isClosedImmersion_map_of_le D g
  let e := limitTailOverEquiv (P := I) i₁
  let Dtail : (LimitTail I i₁)ᵒᵖ ⥤ Scheme.{u} := e.functor ⋙ Over.forget (op i₁) ⋙ D
  let cOver := c.whisker (Over.forget (op i₁))
  let hcOver : IsLimit cOver :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget (op i₁)) c).symm hc
  let ctail := cOver.whisker e.functor
  have hctail : IsLimit ctail := hcOver.whiskerEquivalence e
  let ttail : Dtail ⟶ (Functor.const (LimitTail I i₁)ᵒᵖ).obj S :=
    Functor.whiskerLeft (e.functor ⋙ Over.forget (op i₁)) t
  have hcommTail : ctail.π ≫ ttail = (Functor.const (LimitTail I i₁)ᵒᵖ).map f := by
    ext a
    exact cone_comp_app hcomm (e.functor.obj a).left
  have : Nonempty (LimitTail I i₁) := ⟨⟨i₁, le_rfl⟩⟩
  have : IsDirected (LimitTail I i₁) (· ≤ ·) :=
    { directed := fun a b => by
        obtain ⟨k, hak, hbk⟩ := ‹IsDirected I (· ≤ ·)›.directed a.1 b.1
        exact ⟨⟨k, le_trans a.2 hak⟩, hak, hbk⟩ }
  have : ∀ ⦃a b : LimitTail I i₁⦄ (h : a ≤ b),
      IsClosedImmersion (Dtail.map (homOfLE h).op) := by
    intro a b h
    dsimp [Dtail, e, limitTailOverEquiv]
    infer_instance
  have : ∀ a : LimitTail I i₁, CompactSpace (Dtail.obj (op a)) :=
    fun a => ‹∀ i, CompactSpace (D.obj (op i))› a.1
  have : ∀ a : LimitTail I i₁, QuasiSeparatedSpace (Dtail.obj (op a)) :=
    fun a => ‹∀ i, QuasiSeparatedSpace (D.obj (op i))› a.1
  have : ∀ a : LimitTail I i₁, LocallyOfFiniteType (ttail.app (op a)) :=
    fun a => ‹∀ i, LocallyOfFiniteType (t.app (op i))› a.1
  have hU (a : (LimitTail I i₁)ᵒᵖ) : ttail.app a ⁻¹ᵁ U = ⊤ :=
    hstageTop (e.functor.obj a).left (e.functor.obj a).hom
  obtain ⟨a₀, ha₀⟩ := Filter.eventually_atTop.1
    (eventually_isImmersion_of_preimage_eq_top Dtail ttail ctail hctail f hcommTail U fU hfU hU)
  exact Filter.eventually_atTop.2 ⟨a₀.1, fun k hik => ha₀ ⟨k, a₀.2.trans hik⟩ hik⟩

/-- **Stacks Project, Tag 0GIH.** In a directed inverse system of quasi-compact and
quasi-separated schemes whose transition morphisms are closed immersions, if all the structure
morphisms to a quasi-separated base are locally of finite type and the morphism induced on the
limit is an immersion, then the structure morphisms are immersions for all sufficiently large
indices.
`Nonempty I` is not a weakening: it is what makes `Filter.atTop` on the index a PROPER
filter. Over an empty index `atTop = ⊥` and the conclusion would be vacuously true, so this
hypothesis is what rules vacuity out. The source assumes it too — a directed limit is indexed
by a directed set, which is nonempty by convention. -/
@[stacks 0GIH]
lemma eventually_isImmersion {I : Type v} [Preorder I]
    [IsDirected I (· ≤ ·)] [Small.{u} I]
    {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const Iᵒᵖ).obj S) (c : Cone D) (hc : IsLimit c)
    (f : c.pt ⟶ S)
    [QuasiSeparatedSpace S]
    [∀ i, CompactSpace (D.obj (op i))]
    [∀ i, QuasiSeparatedSpace (D.obj (op i))]
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsClosedImmersion (D.map (homOfLE h).op)]
    [∀ i, LocallyOfFiniteType (t.app (op i))]
    (hcomm : c.π ≫ t = (Functor.const Iᵒᵖ).map f)
    [IsImmersion f] :
    ∀ᶠ i in atTop, IsImmersion (t.app (op i)) := by
  exact eventually_atTop_of_indexSmall D t c hc f (@IsImmersion) inferInstance hcomm
      @fun D' t' c' hc' _ _ _ _ _ f' hf' hcomm' => by
        have := hf'
        exact eventually_isImmersion_of_indexSmall D' t' c' hc' f' hcomm'

end AlgebraicGeometry

end
