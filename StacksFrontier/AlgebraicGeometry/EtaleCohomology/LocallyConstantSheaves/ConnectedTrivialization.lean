module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Point.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.CategoryTheory.Sites.ConstantSheaf.PointFiber
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs

/-!
# Locally constant module sheaves on a connected scheme

If a sheaf of modules is locally constant on the small étale site of a connected scheme, then
one single module suffices to trivialize it throughout an étale covering: the module occurring
on a covering member is locally constant in the member, and on a connected base the set of
members carrying a fixed isomorphism class is clopen, hence everything.

## Main results

* `AlgebraicGeometry.exists_etaleCover_constant`: a locally constant sheaf of modules on a
  connected scheme is locally isomorphic to the constant sheaf of one fixed module.

## Implementation notes

The covering is given by étale schemes over `X` whose images jointly cover `X`. The displayed
isomorphisms compare the restrictions of the given sheaf and of the global constant sheaf to
the slice site over each covering member. The module is chosen once, before the covering.

Comparing the modules on two overlapping members uses a point of the small étale site above a
common point of the base: the fibre functor at that point takes a constant sheaf back to its
module, so the two modules become isomorphic. For that comparison the coefficient category
needs products and colimits indexed by the site, which for `ModuleCat.{v} Λ` requires
`UnivLE.{u, v}`. When that fails every section module is a subsingleton — gluing over an
arbitrarily large disjoint union of one member would otherwise make the index type small — and
the sheaf is isomorphic to the constant sheaf on the trivial module, so the statement holds for
the covering by the identity.

## References

* [Stacks Project, Tag 09BF](https://stacks.math.columbia.edu/tag/09BF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v w uC vC uD vD uA vA

private noncomputable def constantPushforwardIso
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (A : Type uA) [Category.{vA} A]
    [HasWeakSheafify J A] [HasWeakSheafify K A]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.IsContinuous J K] [R.IsContinuous K J]
    {T : D} (hT : IsTerminal T) :
    constantSheaf K A ⋙ L.sheafPushforwardContinuous A J K ≅ constantSheaf J A := by
  letI := adj.isRightAdjoint
  exact ((constantSheafAdj K A hT).comp (adj.sheafPushforwardContinuous J K)).leftAdjointUniq
    (constantSheafAdj J A (hT.isTerminalObj R T))

private noncomputable def overPullbackConstantIso
    {C : Type uC} [Category.{vC} C] [HasFiniteLimits C]
    (J : GrothendieckTopology C) (A : Type uA) [Category.{vA} A]
    [HasWeakSheafify J A] (U : C) [HasWeakSheafify (J.over U) A] (M : A) :
    (J.overPullback A U).obj ((constantSheaf J A).obj M) ≅
      (constantSheaf (J.over U) A).obj M :=
  (constantPushforwardIso (J.over U) J A (Over.forgetAdjStar U) terminalIsTerminal).app M

private noncomputable def overMapPullbackConstantIso
    {C : Type uC} [Category.{vC} C] [HasPullbacks C]
    (J : GrothendieckTopology C) (A : Type uA) [Category.{vA} A]
    {U V : C} [HasWeakSheafify (J.over U) A] [HasWeakSheafify (J.over V) A]
    (f : V ⟶ U) (M : A) :
    (J.overMapPullback A f).obj ((constantSheaf (J.over U) A).obj M) ≅
      (constantSheaf (J.over V) A).obj M :=
  (constantPushforwardIso (J.over V) (J.over U) A (Over.mapPullbackAdj f)
    (Over.mkIdTerminal (X := U))).app M

private lemma modelsIso_of_commonPoint
    {C : Type uC} [Category.{vC} C] [HasPullbacks C] [LocallySmall.{w} C]
    (J : GrothendieckTopology C) (A : Type uA) [Category.{vA} A]
    [∀ U : C, HasWeakSheafify (J.over U) A]
    [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    (F : Sheaf J A) {U V W : C} (g : W ⟶ U) (h : W ⟶ V)
    (p : GrothendieckTopology.Point.{w} J) (x : p.fiber.obj W)
    (M N : A)
    (eU : F.over U ≅ (constantSheaf (J.over U) A).obj M)
    (eV : F.over V ≅ (constantSheaf (J.over V) A).obj N) : Nonempty (M ≅ N) := by
  let q := p.over x
  let r {Z : C} (k : W ⟶ Z) {P : A} (e : F.over Z ≅ (constantSheaf (J.over Z) A).obj P) :=
    q.sheafFiber.mapIso ((F.pushforwardOverMapIso k).symm ≪≫ (J.overMapPullback A k).mapIso e ≪≫
      overMapPullbackConstantIso J A k _) ≪≫
        GrothendieckTopology.Point.constantFiberIso (J.over W) A q _
  exact ⟨(r g eU).symm ≪≫ r h eV⟩

private lemma sections_subsingleton_of_isEmpty
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (Type v))
    (U : X.Etale) [IsEmpty U.left] : Subsingleton (F.obj.obj (op U)) := by
  have h := (isSheaf_iff_isSheaf_of_type _ _).1 F.property
  have hc : Sieve.ofArrows (fun i : Empty => i.elim) (fun i => i.elim) ∈
      X.smallEtaleTopology U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext x
    exact isEmptyElim x
  have hs := (Presieve.isSheafFor_arrows_iff _ _).1 (h.isSheafFor _ hc)
  obtain ⟨_, _, hu⟩ := hs (fun i => i.elim) (fun i => i.elim)
  exact ⟨fun a b => (hu a (fun i => i.elim)).trans (hu b (fun i => i.elim)).symm⟩

/-- Gluing on disjoint unions makes every indexing set small when a section type is nontrivial. -/
private lemma univLE_of_nontrivial_sections
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (Type v))
    (U : X.Etale) [Nontrivial (F.obj.obj (op U))] : UnivLE.{u, v} := by
  classical
  refine ⟨fun I => ?_⟩
  let : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  let V : X.Etale := MorphismProperty.Over.mk ⊤
    (Sigma.desc (fun _ : I => (U.hom : U.left ⟶ X)))
    (IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => U.prop)
  let f : ∀ i : I, U ⟶ V := fun i => MorphismProperty.Over.homMk
    (Sigma.ι (fun _ : I => U.left) i) (by simp [V, MorphismProperty.Over.mk])
  have hf : Sieve.ofArrows (fun _ : I => U) f ∈ X.smallEtaleTopology V := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact (sigmaOpenCover (fun _ : I => U.left)).iUnion_range
  have hs := (isSheaf_iff_isSheaf_of_type _ _).1 F.property
  have hcompat (s : I → F.obj.obj (op U)) : Presieve.Arrows.Compatible F.obj f s := by
    intro i j W a b hab
    by_cases hij : i = j
    · subst j
      rw [(MorphismProperty.Over.Hom.ext ((cancel_mono (Sigma.ι (fun _ : I => U.left) i)).1
        (congrArg (fun k => k.left) hab)) : a = b)]
    · have : IsEmpty W.left := isEmpty_of_commSq_sigmaι_of_ne
        (g := fun _ : I => U.left) (CommSq.mk (congrArg (fun k => k.left) hab)) hij
      exact (sections_subsingleton_of_isEmpty F W).elim _ _
  have hsurj : Function.Surjective
      (fun t : F.obj.obj (op V) => fun i => F.obj.map (f i).op t) := by
    intro s
    obtain ⟨t, ht, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
      (hs.isSheafFor _ hf) s (hcompat s)
    exact ⟨t, funext ht⟩
  have : Small.{v} (I → F.obj.obj (op U)) := small_of_surjective hsurj
  obtain ⟨a, b, hab⟩ := exists_pair_ne (F.obj.obj (op U))
  exact small_of_injective (f := fun i : I => fun j : I => if j = i then a else b)
    fun i j h => of_not_not fun hij => hab (by simpa [hij] using congrFun h i)

private lemma modelsIso_of_inter
    {X : Scheme.{u}} (A : Type uA) [Category.{vA} A]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) A]
    [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
    (F : Sheaf X.smallEtaleTopology A) (U V : X.Etale) (M N : A)
    (eU : F.over U ≅ (constantSheaf (X.smallEtaleTopology.over U) A).obj M)
    (eV : F.over V ≅ (constantSheaf (X.smallEtaleTopology.over V) A).obj N)
    (x : X) (hxU : x ∈ Set.range U.hom) (hxV : x ∈ Set.range V.hom) :
    Nonempty (M ≅ N) := by
  let Ω := SeparableClosure (X.residueField x)
  let s : Spec (.of Ω) ⟶ X := (Scheme.SpecToEquivOfField Ω X).symm
    ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) Ω)⟩
  have hs : s default = x := by simp [s]
  let p := Scheme.pointSmallEtale s
  have fac (Y : X.Etale) (hY : x ∈ Set.range Y.hom) : Nonempty (p.fiber.obj Y) := by
    obtain ⟨a, ha⟩ := hY
    obtain ⟨a', ha', _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed Y.hom s a (ha.trans hs.symm)
    exact ⟨Over.homMk a' ha'⟩
  obtain ⟨a⟩ := fac U hxU
  obtain ⟨b⟩ := fac V hxV
  let u' : p.fiber.Elements := ⟨U, a⟩
  let v' : p.fiber.Elements := ⟨V, b⟩
  exact modelsIso_of_commonPoint X.smallEtaleTopology A F
    (IsCofiltered.minToLeft u' v').val (IsCofiltered.minToRight u' v').val p
    (IsCofiltered.min u' v').2 M N eU eV

private lemma exists_cover_constant_of_products
    (X : Scheme.{u}) [ConnectedSpace X]
    (A : Type uA) [Category.{vA} A]
    [HasWeakSheafify X.smallEtaleTopology A]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) A]
    [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
    (F : Sheaf X.smallEtaleTopology A)
    [Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology F] :
    ∃ (M : A) (I : Type (u + 1)) (U : I → X.Etale),
      ((⋃ i, Set.range (fun x : (U i).left => ((U i).hom : (U i).left ⟶ X) x)) : Set X) =
        Set.univ ∧
        ∀ i, Nonempty ((X.smallEtaleTopology.overPullback A (U i)).obj F ≅
          (X.smallEtaleTopology.overPullback A (U i)).obj
            ((constantSheaf X.smallEtaleTopology A).obj M)) := by
  classical
  let T : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)
  obtain ⟨I, U, f, hf, hU⟩ :=
    Stacks.ConstantSheaf.IsLocallyConstant.exists_cover
      (J := X.smallEtaleTopology) (F := F) T
  let O (i : I) : Set X := Set.range (fun x : (U i).left => ((U i).hom : (U i).left ⟶ X) x)
  have hcover : ((⋃ i, O i) : Set X) = Set.univ := by
    have he (i : I) : (f i).left = (U i).hom := by simpa [T, MorphismProperty.Over.mk] using (f i).w
    have hc := (Scheme.ofArrows_mem_smallEtaleTopology_iff f).1 hf
    change (⋃ i, Set.range (fun x : (U i).left => ((f i).left : (U i).left ⟶ X) x)) =
      (Set.univ : Set X) at hc
    simp only [he] at hc
    exact hc
  have hm (i : I) : ∃ M : A, Nonempty (F.over (U i) ≅
      (constantSheaf (X.smallEtaleTopology.over (U i)) A).obj M) := by
    obtain ⟨M, ⟨e⟩⟩ := (hU i).mem_essImage
    exact ⟨M, ⟨e.symm⟩⟩
  choose M e using hm
  have hmem (x : X) : ∃ i, x ∈ O i := by
    simpa only [← hcover, Set.mem_iUnion] using Set.mem_univ x
  obtain ⟨i₀, hi₀⟩ := hmem (Classical.arbitrary X)
  let S : Set X := ⋃ i : {i : I // Nonempty (M i ≅ M i₀)}, O i.1
  have hopen (s : Set I) : IsOpen (⋃ i : s, O i.1) :=
    isOpen_iUnion fun i => (U i.1).hom.isOpenMap.isOpen_range
  have hcompl : Sᶜ = ⋃ i : {i : I // ¬Nonempty (M i ≅ M i₀)}, O i.1 := by
    ext x
    refine ⟨fun hx => ?_, fun hx hS => ?_⟩
    · obtain ⟨i, hi⟩ := hmem x
      exact Set.mem_iUnion.mpr ⟨⟨i, fun he => hx (Set.mem_iUnion.mpr ⟨⟨i, he⟩, hi⟩)⟩, hi⟩
    · obtain ⟨⟨i, hi⟩, hxi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨⟨j, hj⟩, hxj⟩ := Set.mem_iUnion.mp hS
      obtain ⟨hij⟩ := modelsIso_of_inter A F (U i) (U j) (M i) (M j)
        (e i).some (e j).some x hxi hxj
      exact hi ⟨hij ≪≫ hj.some⟩
  have hS : S = Set.univ := IsClopen.eq_univ
    ⟨isOpen_compl_iff.mp (by rw [hcompl]; exact hopen _), hopen _⟩
    ⟨_, Set.mem_iUnion.mpr ⟨⟨i₀, ⟨Iso.refl _⟩⟩, hi₀⟩⟩
  exact ⟨M i₀, {i : I // Nonempty (M i ≅ M i₀)}, fun i => U i.1, hS, fun i =>
    ⟨(e i.1).some ≪≫ (constantSheaf (X.smallEtaleTopology.over (U i.1)) A).mapIso i.2.some ≪≫
      (overPullbackConstantIso X.smallEtaleTopology A (U i.1) (M i₀)).symm⟩⟩

namespace AlgebraicGeometry

/-- **Stacks 09BF.** On a connected scheme, a locally constant sheaf of modules becomes the
constant sheaf associated to one fixed module after an étale covering. -/
@[stacks 09BF]
public theorem exists_etaleCover_constant
    (X : Scheme.{u}) [ConnectedSpace X]
    (Λ : Type v) [Ring Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))
    [Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology F] :
    ∃ (M : ModuleCat.{v} Λ) (I : Type (u + 1)) (U : I → X.Etale),
      ((⋃ i, Set.range (fun x : (U i).left =>
        (((U i).hom : (U i).left ⟶ X) x))) : Set X) = Set.univ ∧
        ∀ i, Nonempty
          ((X.smallEtaleTopology.overPullback (ModuleCat.{v} Λ) (U i)).obj F ≅
            (X.smallEtaleTopology.overPullback (ModuleCat.{v} Λ) (U i)).obj
              ((constantSheaf X.smallEtaleTopology (ModuleCat.{v} Λ)).obj M)) := by
  classical
  by_cases hsize : UnivLE.{u, v}
  · have : HasLimitsOfSize.{u, u} (ModuleCat.{v} Λ) :=
      hasLimitsOfSizeOfUnivLE.{v, v, u, u} (ModuleCat.{v} Λ)
    exact exists_cover_constant_of_products X (ModuleCat.{v} Λ) F
  · have hsub (G : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) (U : X.Etale) :
        Subsingleton (G.obj.obj (op U)) := by
      by_contra hG
      exact hsize (@univLE_of_nontrivial_sections.{u, v} X
        ((sheafCompose X.smallEtaleTopology (forget (ModuleCat.{v} Λ))).obj G) U
        (not_subsingleton_iff_nontrivial.mp hG))
    let G : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ) :=
      (constantSheaf X.smallEtaleTopology (ModuleCat.{v} Λ)).obj
        (ModuleCat.of Λ PUnit)
    let e : F ≅ G :=
      { hom := 0
        inv := 0
        hom_inv_id := by ext U m; exact (hsub F U.unop).elim _ _
        inv_hom_id := by ext U m; exact (hsub G U.unop).elim _ _ }
    let T : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)
    exact ⟨ModuleCat.of Λ PUnit, PUnit, fun _ => T,
      Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨PUnit.unit, x, rfl⟩,
      fun _ => ⟨(X.smallEtaleTopology.overPullback (ModuleCat.{v} Λ) T).mapIso e⟩⟩

end AlgebraicGeometry
