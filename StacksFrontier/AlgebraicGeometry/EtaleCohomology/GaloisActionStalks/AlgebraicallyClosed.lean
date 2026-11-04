module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisActionStalks.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.SheafStalk
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Étale sheaves over an algebraically closed field

Over an algebraically closed field there is no Galois action to remember: the absolute Galois
group at a geometric point is trivial, because the separable closure of the residue field
inside the field of the geometric point is the residue field itself. Consequently the stalk
functor at the canonical geometric point of `Spec K` is evaluation at the final étale object,
and taking global sections is an equivalence from the small étale topos of `Spec K` to sets.
It follows that the stalk functor at a geometric point `sbar` of an arbitrary scheme `S` is the
functor taking a sheaf to the global sections of its pullback along `sbar`; this is the
alternative definition of the stalk functor.

## Main definitions

* `AlgebraicGeometry.etaleStalkIsoPullbackGlobalSections` — the identification of pullback
  along a geometric point followed by global sections with the stalk functor at that point.

## Main results

* `AlgebraicGeometry.GeometricPoint.subsingleton_absoluteGaloisGroup_of_isAlgClosed` — the
  absolute Galois group at a geometric point of the spectrum of an algebraically closed field
  is trivial.
* `AlgebraicGeometry.globalSections_isEquivalence_of_isAlgClosed` — global sections give an
  equivalence from étale sheaves over an algebraically closed field to sets.
* `AlgebraicGeometry.etaleStalkIsoPullbackGlobalSections_inv_app_etaleStalkGerm` — that
  identification carries the germ of a section over a pointed étale neighbourhood to the
  pullback of that section along the final étale object over the geometric point.

## Implementation notes

The residue field of `Spec K` at the image of a geometric point is the residue field of a prime
ideal of `K`, hence is isomorphic to `K`; so it too is algebraically closed, and the relative
separable closure inside the field of the geometric point is `⊥` by
`IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic`. Two automorphisms of `⊥` over the
base agree because every element of `⊥` comes from the base.

The identity of `Spec K` is a geometric point of `Spec K` once `K` is algebraically closed, and
it lifts uniquely to every étale neighbourhood: a section of an étale morphism over `Spec K` is
determined by the morphism it is a section of. Hence the final étale object, with the identity
lift, is a terminal index for the colimit computing the stalk, so the stalk functor is
evaluation there. Global sections are also evaluation at the final object, and the stalk functor
is an equivalence because it is the composite of the stalk equivalence of Tag 03QT with the
forgetful functor on continuous Galois sets, which is an equivalence for a trivial group.

The alternative description of the stalk functor combines this evaluation description over the
residue field with the comparison of Tag 03Q1 between the stalk of a pullback and the stalk at
the image point. A geometric point is the canonical geometric point of the spectrum of its
residue field composed with its own structure morphism, but only up to `Category.id_comp`; the
two resulting stalk functors are therefore identified through the isomorphism of fibre functors
which that equality of morphisms induces, rather than by transport along an equality of
geometric points.

## References

* [Stacks Project, Tag 04JN](https://stacks.math.columbia.edu/tag/04JN)
* [Stacks Project, Tag 03QX](https://stacks.math.columbia.edu/tag/03QX)
* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Limits

/-- A colimit over a diagram with a terminal index is the value at that index. -/
private def colimitIsoTerminalIndex {C : Type*} [Category* C] {A : Type*} [Category* A]
    [HasColimitsOfShape C A] (F : C ⥤ A) (T : C) (hT : IsTerminal T) :
    colimit F ≅ F.obj T :=
  (colimit.isColimit F).coconePointUniqueUpToIso (colimitOfDiagramTerminal hT F)

/-- The structure map of a colimit over a diagram with a terminal index, composed with the
identification of that colimit, is the map to the terminal index. -/
private lemma colimitIsoTerminalIndex_hom_ι {C : Type*} [Category* C] {A : Type*} [Category* A]
    [HasColimitsOfShape C A] (F : C ⥤ A) (T : C) (hT : IsTerminal T) (X : C) :
    colimit.ι F X ≫ (colimitIsoTerminalIndex F T hT).hom = F.map (hT.from X) := by
  simp [colimitIsoTerminalIndex]

/-- The identification of a colimit over a diagram with a terminal index with the value at that
index is natural in the diagram. -/
private lemma colimitIsoTerminalIndex_naturality {C : Type*} [Category* C] {A : Type*}
    [Category* A] [HasColimitsOfShape C A] {F G : C ⥤ A} (α : F ⟶ G) (T : C)
    (hT : IsTerminal T) :
    colim.map α ≫ (colimitIsoTerminalIndex G T hT).hom =
      (colimitIsoTerminalIndex F T hT).hom ≫ α.app T := by
  apply colimit.hom_ext
  intro X
  calc
    colimit.ι F X ≫ colim.map α ≫ (colimitIsoTerminalIndex G T hT).hom =
        (colimit.ι F X ≫ colim.map α) ≫ (colimitIsoTerminalIndex G T hT).hom := by
          simp [Category.assoc]
    _ = (α.app X ≫ colimit.ι G X) ≫ (colimitIsoTerminalIndex G T hT).hom := by
      rw [colimit.ι_map]
    _ = α.app X ≫ G.map (hT.from X) := by
      rw [Category.assoc, colimitIsoTerminalIndex_hom_ι]
    _ = F.map (hT.from X) ≫ α.app T := (α.naturality (hT.from X)).symm
    _ = (colimit.ι F X ≫ (colimitIsoTerminalIndex F T hT).hom) ≫ α.app T := by
      rw [colimitIsoTerminalIndex_hom_ι]
    _ = colimit.ι F X ≫ (colimitIsoTerminalIndex F T hT).hom ≫ α.app T := by
      simp [Category.assoc]

end CategoryTheory.Limits

namespace AlgebraicGeometry.ContinuousGSet

section

universe v

local instance : HasForget₂ (Type v) TopCat.{v} :=
  { forget₂ := TopCat.discrete
    forget_comp := rfl }

/-- For a trivial group, forgetting the action on a continuous `G`-set is an equivalence onto
sets: every set carries a unique such action and every map of sets is equivariant. -/
private lemma forget_isEquivalence (G : Type u) [Group G] [TopologicalSpace G]
    [Subsingleton G] :
    ((ObjectProperty.ι _ : DiscreteContAction (Type v) G ⥤ ContAction (Type v) G) ⋙
      (ObjectProperty.ι _ : ContAction (Type v) G ⥤ Action (Type v) G) ⋙
      Action.forget (Type v) G).IsEquivalence := by
  let : (Action.forget (Type v) G).Full := {
    map_surjective {X Y} f := by
      refine ⟨{ hom := f, comm := ?_ }, rfl⟩
      intro g
      have hX : X.ρ g = 𝟙 X.V := by rw [Subsingleton.elim g 1]; simp
      have hY : Y.ρ g = 𝟙 Y.V := by rw [Subsingleton.elim g 1]; simp
      rw [hX, hY]
      exact (Category.id_comp f).trans (Category.comp_id f).symm }
  let F := (ObjectProperty.ι _ : DiscreteContAction (Type v) G ⥤ ContAction (Type v) G) ⋙
    (ObjectProperty.ι _ : ContAction (Type v) G ⥤ Action (Type v) G) ⋙
    Action.forget (Type v) G
  let : F.EssSurj := {
    mem_essImage X := by
      let Y : ContAction (Type v) G := ⟨Action.trivial G X, by
        rw [Action.isContinuous_def]
        exact continuous_snd⟩
      let Z : DiscreteContAction (Type v) G := ⟨Y, by
        exact inferInstanceAs (DiscreteTopology (TopCat.discrete.obj X))⟩
      exact ⟨Z, ⟨Iso.refl _⟩⟩ }
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end

end AlgebraicGeometry.ContinuousGSet

namespace AlgebraicGeometry

namespace GeometricPoint

variable (K : Type u) [Field K] [IsAlgClosed K] (s : GeometricPoint (Spec (.of K)))

/-- **Stacks Project, Tag 04JN.** An algebraically closed field has trivial absolute Galois
group at every geometric point of its spectrum. -/
@[stacks 04JN "trivial absolute Galois group"]
theorem subsingleton_absoluteGaloisGroup_of_isAlgClosed :
    Subsingleton (absoluteGaloisGroup s) := by
  classical
  let := residueFieldAlgebra s
  let F : Type u := (Spec (.of K)).residueField (s.hom default)
  let E := s.residueField
  let L := separableClosure s
  let p := (s.hom default).asIdeal
  have hp : p.IsPrime := (s.hom default).2
  let := hp
  let i := Scheme.Spec.residueFieldIso (.of K) (s.hom default)
  let e : K ≃+* F := p.algEquivResidueFieldOfField.toRingEquiv.trans
    i.symm.commRingCatIsoToRingEquiv
  let : IsAlgClosed F := ⟨fun q => by
    convert (IsAlgClosed.splits (q.map e.symm)).map e.toRingHom using 1
    rw [Polynomial.map_map]
    simp⟩
  have hL : L = (⊥ : IntermediateField F E) :=
    IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic L
  refine ⟨fun σ τ => AlgEquiv.ext fun x => ?_⟩
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp (show (x : E) ∈ (⊥ : IntermediateField F E) by
    rw [← hL]; exact x.2)
  rw [show x = algebraMap F L y from Subtype.ext hy.symm]
  exact (σ.commutes y).trans (τ.commutes y).symm

end GeometricPoint

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] [IsAlgClosed K]
  (hK : B.Contains (Spec (.of K)))

/-- The identity of the spectrum of an algebraically closed field, as a geometric point of that
spectrum. -/
private abbrev canonicalGeometricPoint : GeometricPoint (Spec (.of K)) :=
  ⟨K, 𝟙 (Spec (.of K))⟩

/-- The final étale object, with the identity as lift, as a pointed étale neighbourhood of the
canonical geometric point of the spectrum of an algebraically closed field. -/
private abbrev canonicalPointFinalElement :
    (geometricPointFiber B (Spec (.of K)) hK (canonicalGeometricPoint K)).Elements :=
  ⟨SmallEtale.final B (Spec (.of K)) hK,
    ⟨𝟙 (Spec (.of K)), by simp [SmallEtale.final, canonicalGeometricPoint]⟩⟩

/-- The final étale object with the identity lift is a terminal index for the colimit computing
the stalk at the canonical geometric point: an étale neighbourhood of that point is an étale
scheme over `Spec K` with a section, and a section determines a unique map from the final
object. -/
private def canonicalPointFiberTerminalIndex :
    IsTerminal (op (canonicalPointFinalElement B K hK)) := by
  let s : GeometricPoint (Spec (.of K)) := canonicalGeometricPoint K
  let xT := (canonicalPointFinalElement B K hK).2
  let eT := canonicalPointFinalElement B K hK
  let lift (X : (geometricPointFiber B (Spec (.of K)) hK s).Elements) : eT ⟶ X := by
    rcases X with ⟨V, x⟩
    let q : B.inclusion.obj (B.obj (Spec (.of K)) hK) ⟶
        B.inclusion.obj V.obj.left := x.1
    have hq : (B.inclusion.preimage q) ≫ V.obj.hom = 𝟙 (B.obj (Spec (.of K)) hK) := by
      apply B.inclusion.map_injective
      rw [B.inclusion.map_comp, B.inclusion.map_preimage, B.inclusion.map_id]
      simpa [q, s] using x.2
    let f : eT.1 ⟶ V := ObjectProperty.homMk (Over.homMk (B.inclusion.preimage q) hq)
    have hf : (geometricPointFiber B (Spec (.of K)) hK s).map f xT = x := by
      apply Subtype.ext
      change 𝟙 (Spec (.of K)) ≫ B.inclusion.map (B.inclusion.preimage q) = q
      rw [B.inclusion.map_preimage]
      simp
    exact CategoryOfElements.homMk _ _ f hf
  refine IsTerminal.ofUniqueHom (fun X => (lift X.unop).op) (fun X f => ?_)
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  apply (SmallEtale.toScheme B (Spec (.of K)) hK).map_injective
  have hv := congrArg Subtype.val (f.unop.property.trans (lift X.unop).property.symm)
  dsimp [geometricPointFiber] at hv
  change xT.1 ≫ (SmallEtale.toScheme B (Spec (.of K)) hK).map f.unop.val =
    xT.1 ≫ (SmallEtale.toScheme B (Spec (.of K)) hK).map (lift X.unop).val at hv
  simp only [xT] at hv
  exact hv

/-- The stalk at the canonical geometric point of the spectrum of an algebraically closed field
is evaluation at the final étale object. -/
private def etaleStalkIsoEvaluationAtCanonicalPoint :
    etaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK (canonicalGeometricPoint K) ≅
      sheafToPresheaf (SmallEtale.topology B (Spec (.of K)) hK) (Type (u + 1)) ⋙
        (evaluation _ _).obj (op (SmallEtale.final B (Spec (.of K)) hK)) := by
  let s : GeometricPoint (Spec (.of K)) := canonicalGeometricPoint K
  let tI := op (canonicalPointFinalElement B K hK)
  have htI : IsTerminal tI := canonicalPointFiberTerminalIndex B K hK
  refine NatIso.ofComponents (fun F => colimitIsoTerminalIndex
    ((CategoryOfElements.π (geometricPointFiber B (Spec (.of K)) hK s)).op ⋙ F.obj)
    tI htI) ?_
  intro F G α
  exact colimitIsoTerminalIndex_naturality (Functor.whiskerLeft
    (CategoryOfElements.π (geometricPointFiber B (Spec (.of K)) hK s)).op α.hom) tI htI

/-- **Stacks Project, Tag 04JN.** Over an algebraically closed field, taking global sections is
an equivalence from the small étale topos to the category of sets. -/
@[stacks 04JN "equivalence by global sections"]
theorem globalSections_isEquivalence_of_isAlgClosed :
    (Sheaf.Γ (SmallEtale.topology B (Spec (.of K)) hK) (Type (u + 1))).IsEquivalence := by
  let s : GeometricPoint (Spec (.of K)) := canonicalGeometricPoint K
  let E := etaleSheafStalkEquivalence.{u, u + 1} B K hK s
  let : Subsingleton (GeometricPoint.absoluteGaloisGroup s) :=
    GeometricPoint.subsingleton_absoluteGaloisGroup_of_isAlgClosed K s
  let : (AlgebraicGeometry.ContinuousGSet.forget.{u, u + 1}
      (GeometricPoint.absoluteGaloisGroup s)).IsEquivalence :=
    AlgebraicGeometry.ContinuousGSet.forget_isEquivalence
      (GeometricPoint.absoluteGaloisGroup s)
  let : (etaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK s).IsEquivalence :=
    Functor.isEquivalence_of_iso E.2.1
  exact Functor.isEquivalence_of_iso
    (etaleStalkIsoEvaluationAtCanonicalPoint B K hK ≪≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (SmallEtale.finalIsTerminal B (Spec (.of K)) hK)).symm)

/-- Under the identification of the stalk at the canonical geometric point with evaluation at
the final étale object, the germ of a section over the final object is that section. -/
private lemma etaleStalkIsoEvaluationAtCanonicalPoint_hom_app_etaleStalkGerm
    (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) (Type (u + 1)))
    (z : F.obj.obj (op (SmallEtale.final B (Spec (.of K)) hK))) :
    (etaleStalkIsoEvaluationAtCanonicalPoint B K hK).hom.app F
        (etaleStalkGerm.{u, u + 1} B (Spec (.of K)) hK (canonicalGeometricPoint K) F
          (canonicalPointFinalElement B K hK) z) = z := by
  let tI : (geometricPointFiber B (Spec (.of K)) hK
    (canonicalGeometricPoint K)).Elementsᵒᵖ := op (canonicalPointFinalElement B K hK)
  let hI : IsTerminal tI := canonicalPointFiberTerminalIndex B K hK
  let G := (CategoryOfElements.π (geometricPointFiber B (Spec (.of K)) hK
    (canonicalGeometricPoint K))).op ⋙ F.obj
  show (colimitIsoTerminalIndex G tI hI).hom (colimit.ι G tI z) = z
  have hfrom : hI.from tI = 𝟙 tI := hI.hom_ext _ _
  have hz := congrArg (fun k => k z) (colimitIsoTerminalIndex_hom_ι G tI hI tI)
  simpa [hfrom] using hz

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- A geometric point is the canonical geometric point of the spectrum of its residue field,
composed with its own structure morphism. -/
private lemma canonicalGeometricPoint_map_hom (s : GeometricPoint S)
    (hK : B.Contains (Spec (.of s.residueField))) :
    ((canonicalGeometricPoint s.residueField).map
        (B.inclusion.map (⟨s.hom⟩ : (⟨Spec (.of s.residueField), hK⟩ : B.Scheme) ⟶
          (⟨S, hS⟩ : B.Scheme)))).hom =
      s.hom :=
  Category.id_comp s.hom

/-- The lifts of a geometric point and the lifts of its factorization through the canonical
geometric point of the spectrum of its residue field are the same, naturally in the étale
neighbourhood. -/
private def canonicalGeometricPointFiberIso (s : GeometricPoint S)
    (hK : B.Contains (Spec (.of s.residueField))) :
    geometricPointFiber B S hS
        ((canonicalGeometricPoint s.residueField).map
          (B.inclusion.map (⟨s.hom⟩ : (⟨Spec (.of s.residueField), hK⟩ : B.Scheme) ⟶
            (⟨S, hS⟩ : B.Scheme)))) ≅
      geometricPointFiber B S hS s :=
  NatIso.ofComponents
    (fun _ => Equiv.toIso
      { toFun := fun p => ⟨p.1, p.2.trans (canonicalGeometricPoint_map_hom B S hS s hK)⟩
        invFun := fun p => ⟨p.1, p.2.trans (canonicalGeometricPoint_map_hom B S hS s hK).symm⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    (fun _ => rfl)

/-- If the forward component of an isomorphism of `Type`-valued functors sends `x` to `y`, its
inverse component sends `y` back to `x`. -/
private lemma inv_app_eq_of_hom_app_eq {C : Type*} [Category* C] {F G : C ⥤ Type u} (e : F ≅ G)
    (X : C) {x : F.obj X} {y : G.obj X} (h : e.hom.app X x = y) : e.inv.app X y = x := by
  rw [← h, ← CategoryTheory.comp_apply, e.hom_inv_id_app, CategoryTheory.id_apply]

/-- **Stacks Project, Tag 04JN.** The alternative description of the stalk functor at a
geometric point `sbar` of `S`: it is the functor sending a sheaf to the global sections of its
pullback along `sbar`. -/
@[stacks 04JN "the stalk as global sections of the pullback", no_expose]
def etaleStalkIsoPullbackGlobalSections (s : GeometricPoint S)
    (hK : B.Contains (Spec (.of s.residueField))) :
    letI : (smallEtaleBaseChange B (⟨s.hom⟩ :
        (⟨Spec (.of s.residueField), hK⟩ : B.Scheme) ⟶ (⟨S, hS⟩ : B.Scheme))).IsContinuous
        (SmallEtale.topology B S hS)
        (SmallEtale.topology B (Spec (.of s.residueField)) hK) :=
      smallEtaleBaseChange_isContinuous B
        (⟨s.hom⟩ : (⟨Spec (.of s.residueField), hK⟩ : B.Scheme) ⟶ (⟨S, hS⟩ : B.Scheme))
    (smallEtaleBaseChange B (⟨s.hom⟩ : (⟨Spec (.of s.residueField), hK⟩ : B.Scheme) ⟶
            (⟨S, hS⟩ : B.Scheme))).sheafPullback (Type (u + 1)) (SmallEtale.topology B S hS)
          (SmallEtale.topology B (Spec (.of s.residueField)) hK) ⋙
        Sheaf.Γ (SmallEtale.topology B (Spec (.of s.residueField)) hK) (Type (u + 1)) ≅
      etaleStalkFunctor.{u, u + 1} B S hS s :=
  let f : (⟨Spec (.of s.residueField), hK⟩ : B.Scheme) ⟶ (⟨S, hS⟩ : B.Scheme) := ⟨s.hom⟩
  letI : (smallEtaleBaseChange B f).IsContinuous (SmallEtale.topology B S hS)
      (SmallEtale.topology B (Spec (.of s.residueField)) hK) :=
    smallEtaleBaseChange_isContinuous B f
  let P := (smallEtaleBaseChange B f).sheafPullback (Type (u + 1))
    (SmallEtale.topology B S hS) (SmallEtale.topology B (Spec (.of s.residueField)) hK)
  let σ : P ⋙ etaleStalkFunctor.{u, u + 1} B (Spec (.of s.residueField)) hK
        (canonicalGeometricPoint s.residueField) ≅
      etaleStalkFunctor.{u, u + 1} B S hS
        ((canonicalGeometricPoint s.residueField).map (B.inclusion.map f)) :=
    smallEtalePullbackStalkIso B f (canonicalGeometricPoint s.residueField)
  let δ : etaleStalkFunctor.{u, u + 1} B S hS
        ((canonicalGeometricPoint s.residueField).map (B.inclusion.map f)) ≅
      etaleStalkFunctor.{u, u + 1} B S hS s :=
    CategoryOfElements.sheafColimIsoOfNatIso (SmallEtale.topology B S hS)
      (canonicalGeometricPointFiberIso B S hS s hK)
  Functor.isoWhiskerLeft P (Sheaf.ΓNatIsoSheafSections
      (SmallEtale.topology B (Spec (.of s.residueField)) hK) (Type (u + 1))
      (SmallEtale.finalIsTerminal B (Spec (.of s.residueField)) hK)) ≪≫
    Functor.isoWhiskerLeft P
      (etaleStalkIsoEvaluationAtCanonicalPoint B s.residueField hK).symm ≪≫ σ ≪≫ δ

/-- **Stacks Project, Tag 04JN.** The alternative description of the stalk functor is the
canonical comparison: it carries the germ at `sbar` of a section over a pointed étale
neighbourhood to the section of the pullback obtained by restricting along the corresponding
morphism from the final étale object over `sbar`. -/
@[stacks 04JN "the comparison on germs"]
theorem etaleStalkIsoPullbackGlobalSections_inv_app_etaleStalkGerm (s : GeometricPoint S)
    (hK : B.Contains (Spec (.of s.residueField)))
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))
    (V : (geometricPointFiber B S hS s).Elements)
    (a : SmallEtale.final B (Spec (.of s.residueField)) hK ⟶
      (smallEtaleBaseChange B (⟨s.hom⟩ : (⟨Spec (.of s.residueField), hK⟩ : B.Scheme) ⟶
        (⟨S, hS⟩ : B.Scheme))).obj V.1)
    (ha : (SmallEtale.toScheme B (Spec (.of s.residueField)) hK).map a ≫
      B.inclusion.map (pullback.fst V.1.obj.hom
        (⟨s.hom⟩ : (⟨Spec (.of s.residueField), hK⟩ : B.Scheme) ⟶
          (⟨S, hS⟩ : B.Scheme))) = V.2.1)
    (t : F.obj.obj (op V.1)) :
    letI : (smallEtaleBaseChange B (⟨s.hom⟩ :
        (⟨Spec (.of s.residueField), hK⟩ : B.Scheme) ⟶ (⟨S, hS⟩ : B.Scheme))).IsContinuous
        (SmallEtale.topology B S hS)
        (SmallEtale.topology B (Spec (.of s.residueField)) hK) :=
      smallEtaleBaseChange_isContinuous B
        (⟨s.hom⟩ : (⟨Spec (.of s.residueField), hK⟩ : B.Scheme) ⟶ (⟨S, hS⟩ : B.Scheme))
    (Sheaf.ΓNatIsoSheafSections (SmallEtale.topology B (Spec (.of s.residueField)) hK)
          (Type (u + 1))
          (SmallEtale.finalIsTerminal B (Spec (.of s.residueField)) hK)).hom.app
        (((smallEtaleBaseChange B (⟨s.hom⟩ :
            (⟨Spec (.of s.residueField), hK⟩ : B.Scheme) ⟶
              (⟨S, hS⟩ : B.Scheme))).sheafPullback (Type (u + 1))
              (SmallEtale.topology B S hS)
              (SmallEtale.topology B (Spec (.of s.residueField)) hK)).obj F)
        ((etaleStalkIsoPullbackGlobalSections B S hS s hK).inv.app F
          (etaleStalkGerm.{u, u + 1} B S hS s F V t)) =
      pullbackSectionAlong B (⟨s.hom⟩ : (⟨Spec (.of s.residueField), hK⟩ : B.Scheme) ⟶
          (⟨S, hS⟩ : B.Scheme)) F V.1
        (SmallEtale.final B (Spec (.of s.residueField)) hK) a t := by
  let f : (⟨Spec (.of s.residueField), hK⟩ : B.Scheme) ⟶ (⟨S, hS⟩ : B.Scheme) := ⟨s.hom⟩
  have : (smallEtaleBaseChange B f).IsContinuous (SmallEtale.topology B S hS)
      (SmallEtale.topology B (Spec (.of s.residueField)) hK) :=
    smallEtaleBaseChange_isContinuous B f
  let s₀ : GeometricPoint (Spec (.of s.residueField)) := canonicalGeometricPoint s.residueField
  let P := (smallEtaleBaseChange B f).sheafPullback (Type (u + 1))
    (SmallEtale.topology B S hS) (SmallEtale.topology B (Spec (.of s.residueField)) hK)
  let γ := Sheaf.ΓNatIsoSheafSections
    (SmallEtale.topology B (Spec (.of s.residueField)) hK) (Type (u + 1))
    (SmallEtale.finalIsTerminal B (Spec (.of s.residueField)) hK)
  let β := etaleStalkIsoEvaluationAtCanonicalPoint B s.residueField hK
  let σ : P ⋙ etaleStalkFunctor.{u, u + 1} B (Spec (.of s.residueField)) hK s₀ ≅
      etaleStalkFunctor.{u, u + 1} B S hS (s₀.map (B.inclusion.map f)) :=
    smallEtalePullbackStalkIso B f s₀
  let δ : etaleStalkFunctor.{u, u + 1} B S hS (s₀.map (B.inclusion.map f)) ≅
      etaleStalkFunctor.{u, u + 1} B S hS s :=
    CategoryOfElements.sheafColimIsoOfNatIso (SmallEtale.topology B S hS)
      (canonicalGeometricPointFiberIso B S hS s hK)
  let U : (geometricPointFiber B (Spec (.of s.residueField)) hK s₀).Elements :=
    canonicalPointFinalElement B s.residueField hK
  let V₀ : (geometricPointFiber B S hS (s₀.map (B.inclusion.map f))).Elements :=
    ⟨V.1, ⟨V.2.1, V.2.2.trans (canonicalGeometricPoint_map_hom B S hS s hK).symm⟩⟩
  have hδ : δ.inv.app F (etaleStalkGerm.{u, u + 1} B S hS s F V t) =
      etaleStalkGerm.{u, u + 1} B S hS (s₀.map (B.inclusion.map f)) F V₀ t := by
    have h := congrArg (fun k => k t) (CategoryOfElements.ι_sheafColimIsoOfNatIso_hom
      (SmallEtale.topology B S hS) (canonicalGeometricPointFiberIso B S hS s hK) F V₀)
    rw [CategoryTheory.comp_apply] at h
    have h' : δ.hom.app F
        (etaleStalkGerm.{u, u + 1} B S hS (s₀.map (B.inclusion.map f)) F V₀ t) =
        etaleStalkGerm.{u, u + 1} B S hS s F V t := h
    exact inv_app_eq_of_hom_app_eq δ F h'
  have hσ : σ.inv.app F
        (etaleStalkGerm.{u, u + 1} B S hS (s₀.map (B.inclusion.map f)) F V₀ t) =
      etaleStalkGerm.{u, u + 1} B (Spec (.of s.residueField)) hK s₀ (P.obj F) U
        (pullbackSectionAlong B f F V.1 (SmallEtale.final B (Spec (.of s.residueField)) hK)
          a t) := by
    have haU : U.2.1 ≫ (SmallEtale.toScheme B (Spec (.of s.residueField)) hK).map a ≫
        B.inclusion.map (pullback.fst V₀.1.obj.hom f) = V₀.2.1 :=
      (Category.id_comp _).trans ha
    have h' : σ.hom.app F
        (etaleStalkGerm.{u, u + 1} B (Spec (.of s.residueField)) hK s₀ (P.obj F) U
          (pullbackSectionAlong B f F V.1
            (SmallEtale.final B (Spec (.of s.residueField)) hK) a t)) =
        etaleStalkGerm.{u, u + 1} B S hS (s₀.map (B.inclusion.map f)) F V₀ t :=
      smallEtalePullbackStalkIso_germ B f s₀ F U V₀ a haU t
    exact inv_app_eq_of_hom_app_eq σ F h'
  show γ.hom.app (P.obj F)
      (γ.inv.app (P.obj F) (β.hom.app (P.obj F) (σ.inv.app F
        (δ.inv.app F (etaleStalkGerm.{u, u + 1} B S hS s F V t))))) = _
  rw [hδ, hσ, ← CategoryTheory.comp_apply, γ.inv_hom_id_app, CategoryTheory.id_apply]
  exact etaleStalkIsoEvaluationAtCanonicalPoint_hom_app_etaleStalkGerm B s.residueField hK
    (P.obj F) _

end AlgebraicGeometry

end
