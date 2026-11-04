module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Extension of scalars preserves constructible étale sheaves

A constructible sheaf of modules on the small étale site remains constructible after extending
scalars along a homomorphism of Noetherian rings.

## Main results

* `AlgebraicGeometry.SmallEtale.isConstructibleModuleSheaf_extendScalars`: constructibility is
  preserved by sheafified extension of scalars.

## Implementation notes

The tensor product with the constant sheaf of the target ring is represented by sheafifying the
sectionwise tensor product, which is `Sheaf.composeAndSheafify` of
`ModuleCat.extendScalars`. No separate sheaf-level extension-of-scalars functor is introduced:
the composite `sheafToPresheaf ⋙ whiskeringRight ⋙ presheafToSheaf` is `Sheaf.composeAndSheafify`
on the nose.

The proof is local on a constructible stratification: the same stratification witnesses
constructibility after extension of scalars, so the work is to see that extension of scalars
commutes with restriction to a stratum and sends a locally constant sheaf of finitely generated
modules to one of the same kind. Commutation is an instance of uniqueness of left adjoints: both
composites are left adjoint to the composite of restriction of scalars with pushforward, in the
two possible orders, and those two right adjoints agree up to a natural isomorphism which is the
identity on components.

Finite generation is preserved because extension of scalars is base change of modules, and local
constancy because extension of scalars carries a constant sheaf to the constant sheaf on the
extended value — again by uniqueness of left adjoints, through
`presheafToSheafCompComposeAndSheafifyIso`.

Sheafification on the small étale site of a stratum is not assumed: it is deduced from
sheafification on its localizations, since the small étale site has a final object, and
localizing at a final object is an equivalence of sites.

## References

* [Stacks Project, Tag 0GKB](https://stacks.math.columbia.edu/tag/0GKB)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w r s v c

namespace AlgebraicGeometry.SmallEtale

/-- Extension of scalars along a ring homomorphism preserves finite generation, because it is
base change of modules. -/
public lemma isFG_extendScalars {R : Type r} {S : Type s}
    [CommRing R] [CommRing S] (f : R →+* S) (E : ModuleCat.{max r s w} R)
    (hE : ModuleCat.isFG R E) :
    ModuleCat.isFG S ((ModuleCat.extendScalars f).obj E) := by
  rw [ModuleCat.isFG_iff] at hE ⊢
  let _ : Algebra R S := f.toAlgebra
  exact Module.Finite.base_change R S E

/-- Sheafified extension of scalars carries the constant sheaf on a module to the constant
sheaf on its extension of scalars. -/
private noncomputable def extendScalarsConstantSheafIso
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type r) (S : Type s) [CommRing R] [CommRing S]
    [HasWeakSheafify J (ModuleCat.{max r s w} R)]
    [HasWeakSheafify J (ModuleCat.{max r s w} S)]
    (f : R →+* S) (E : ModuleCat.{max r s w} R) :
    (Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{r, s, max r s w} f)).obj
        ((constantSheaf J (ModuleCat.{max r s w} R)).obj E) ≅
      (constantSheaf J (ModuleCat.{max r s w} S)).obj
        ((ModuleCat.extendScalars f).obj E) := by
  let adj := ModuleCat.extendRestrictScalarsAdj.{max r s w, r, s} f
  have : J.PreservesSheafification (ModuleCat.extendScalars.{r, s, max r s w} f) :=
    Sheaf.preservesSheafification_of_adjunction J adj
  exact ((presheafToSheafCompComposeAndSheafifyIso J
      (ModuleCat.extendScalars.{r, s, max r s w} f)).app
        ((Functor.const Cᵒᵖ).obj E)) ≪≫
    (presheafToSheaf J (ModuleCat.{max r s w} S)).mapIso
      (Functor.constComp Cᵒᵖ E (ModuleCat.extendScalars.{r, s, max r s w} f))

/-- Restriction of scalars along `f` lifts to sheaves on any site, because it is continuous: it
preserves limits, being a right adjoint. -/
private lemma hasSheafCompose_restrictScalars {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) {R : Type r} {S : Type s} [CommRing R] [CommRing S]
    (f : R →+* S) :
    J.HasSheafCompose (ModuleCat.restrictScalars.{max r s w, r, s} f) := by
  have : Limits.PreservesLimitsOfSize.{v, max c v}
      (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    (ModuleCat.extendRestrictScalarsAdj.{max r s w, r, s} f).rightAdjoint_preservesLimits
  exact ⟨fun P hP ↦ Presheaf.isSheaf_comp_of_isSheaf J P _ hP⟩

/-- Sheafified extension of scalars commutes with a functor between categories of sheaves
admitting a right adjoint, provided the right adjoints commute with restriction of scalars. -/
private noncomputable def extendScalarsAppIso
    {C : Type c} {C' : Type*} [Category.{v} C] [Category.{v} C']
    (J : GrothendieckTopology C) (K : GrothendieckTopology C')
    (R : Type r) (S : Type s) [CommRing R] [CommRing S]
    (f : R →+* S)
    [HasWeakSheafify J (ModuleCat.{max r s w} S)]
    [HasWeakSheafify K (ModuleCat.{max r s w} S)]
    [J.HasSheafCompose (ModuleCat.restrictScalars.{max r s w, r, s} f)]
    [K.HasSheafCompose (ModuleCat.restrictScalars.{max r s w, r, s} f)]
    {LR : Sheaf J (ModuleCat.{max r s w} R) ⥤ Sheaf K (ModuleCat.{max r s w} R)}
    {LS : Sheaf J (ModuleCat.{max r s w} S) ⥤ Sheaf K (ModuleCat.{max r s w} S)}
    {PR : Sheaf K (ModuleCat.{max r s w} R) ⥤ Sheaf J (ModuleCat.{max r s w} R)}
    {PS : Sheaf K (ModuleCat.{max r s w} S) ⥤ Sheaf J (ModuleCat.{max r s w} S)}
    (pR : LR ⊣ PR) (pS : LS ⊣ PS)
    (hP : PS ⋙ sheafCompose J (ModuleCat.restrictScalars.{max r s w, r, s} f) ≅
      sheafCompose K (ModuleCat.restrictScalars.{max r s w, r, s} f) ⋙ PR)
    (F : Sheaf J (ModuleCat.{max r s w} R)) :
    (Sheaf.composeAndSheafify K (ModuleCat.extendScalars.{r, s, max r s w} f)).obj
        (LR.obj F) ≅
      LS.obj ((Sheaf.composeAndSheafify J
        (ModuleCat.extendScalars.{r, s, max r s w} f)).obj F) := by
  let eJ := Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{max r s w, r, s} f)
  let eK := Sheaf.adjunction K (ModuleCat.extendRestrictScalarsAdj.{max r s w, r, s} f)
  simpa [Sheaf.composeAndSheafify] using
    (Adjunction.leftAdjointUniq (pR.comp eK) ((eJ.comp pS).ofNatIsoRight hP)).app F

/-- Sheafified extension of scalars commutes with restriction to a localization of the site. -/
private noncomputable def overPullbackExtendScalarsAppIso
    {C : Type c} [Category.{v} C] [Limits.HasBinaryProducts C]
    (J : GrothendieckTopology C) (U : C)
    (R : Type r) (S : Type s) [CommRing R] [CommRing S]
    (f : R →+* S)
    [HasWeakSheafify J (ModuleCat.{max r s w} S)]
    [HasWeakSheafify (J.over U) (ModuleCat.{max r s w} S)]
    (F : Sheaf J (ModuleCat.{max r s w} R)) :
    (Sheaf.composeAndSheafify (J.over U)
          (ModuleCat.extendScalars.{r, s, max r s w} f)).obj
        ((J.overPullback (ModuleCat.{max r s w} R) U).obj F) ≅
      (J.overPullback (ModuleCat.{max r s w} S) U).obj
        ((Sheaf.composeAndSheafify J
          (ModuleCat.extendScalars.{r, s, max r s w} f)).obj F) := by
  have := hasSheafCompose_restrictScalars.{w} J f
  have := hasSheafCompose_restrictScalars.{w} (J.over U) f
  exact extendScalarsAppIso J (J.over U) R S f
    ((Over.forgetAdjStar U).sheafPushforwardContinuous
      (E := ModuleCat.{max r s w} R) (J.over U) J)
    ((Over.forgetAdjStar U).sheafPushforwardContinuous
      (E := ModuleCat.{max r s w} S) (J.over U) J)
    (by exact NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)) F

/-- Sheafified extension of scalars commutes with inverse image along a continuous functor. -/
private noncomputable def sheafPullbackExtendScalarsAppIso
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Functor.IsContinuous G J K]
    (R : Type r) (S : Type s) [CommRing R] [CommRing S]
    (f : R →+* S)
    [HasWeakSheafify J (ModuleCat.{max r s w} S)]
    [HasWeakSheafify K (ModuleCat.{max r s w} S)]
    [(G.sheafPushforwardContinuous (ModuleCat.{max r s w} R) J K).IsRightAdjoint]
    [(G.sheafPushforwardContinuous (ModuleCat.{max r s w} S) J K).IsRightAdjoint]
    (F : Sheaf J (ModuleCat.{max r s w} R)) :
    (Sheaf.composeAndSheafify K (ModuleCat.extendScalars.{r, s, max r s w} f)).obj
        ((G.sheafPullback (ModuleCat.{max r s w} R) J K).obj F) ≅
      (G.sheafPullback (ModuleCat.{max r s w} S) J K).obj
        ((Sheaf.composeAndSheafify J
          (ModuleCat.extendScalars.{r, s, max r s w} f)).obj F) := by
  have := hasSheafCompose_restrictScalars.{w} J f
  have := hasSheafCompose_restrictScalars.{w} K f
  exact extendScalarsAppIso J K R S f
    (G.sheafAdjunctionContinuous (ModuleCat.{max r s w} R) J K)
    (G.sheafAdjunctionContinuous (ModuleCat.{max r s w} S) J K)
    (by exact NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)) F

/-- Extension of scalars preserves local constancy with finitely generated values. -/
private theorem isFiniteTypeLocallyConstant_extendScalars
    {C : Type c} [Category.{v} C] [Limits.HasBinaryProducts C]
    (J : GrothendieckTopology C)
    (R : Type r) (S : Type s) [CommRing R] [CommRing S]
    [HasWeakSheafify J (ModuleCat.{max r s w} S)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max r s w} R)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max r s w} S)]
    (f : R →+* S) (F : Sheaf J (ModuleCat.{max r s w} R))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R J F) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant S J
      ((Sheaf.composeAndSheafify J
        (ModuleCat.extendScalars.{r, s, max r s w} f)).obj F) := by
  intro U
  obtain ⟨I, V, g, hg, hV⟩ := hF U
  refine ⟨I, V, g, hg, fun i ↦ ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := hV i
  refine ⟨(ModuleCat.extendScalars.{r, s, max r s w} f).obj E,
    isFG_extendScalars f E hE, ?_⟩
  exact ⟨(extendScalarsConstantSheafIso (J.over (V i)) R S f E).symm ≪≫
    (Sheaf.composeAndSheafify (J.over (V i))
      (ModuleCat.extendScalars.{r, s, max r s w} f)).mapIso e ≪≫
    overPullbackExtendScalarsAppIso J (V i) R S f F⟩

/-- Local constancy with finitely generated values is an isomorphism-invariant property. -/
private theorem isFiniteTypeLocallyConstant_of_iso
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type r) [Ring R]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} R)]
    {F G : Sheaf J (ModuleCat.{w} R)} (e : F ≅ G)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R J F) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R J G := by
  intro U
  obtain ⟨I, V, f, hf, h⟩ := hF U
  refine ⟨I, V, f, hf, fun i ↦ ?_⟩
  obtain ⟨E, hE, ⟨e₀⟩⟩ := h i
  exact ⟨E, hE, ⟨e₀ ≪≫ (J.overPullback (ModuleCat.{w} R) (V i)).mapIso e⟩⟩

/-- The equivalence of a site with its localization at a final object is cocontinuous. A sieve
covering an object of the localization pulls back to the sieve the localization assigned to it,
since every arrow into an object over a final object factors through the canonical isomorphism
onto that object's own slice presentation. -/
private lemma isCocontinuous_equivalenceOfIsTerminal {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) {T : C} (hT : Limits.IsTerminal T) :
    (Over.equivalenceOfIsTerminal hT).symm.functor.IsCocontinuous J (J.over T) := by
  refine ⟨fun {U} S hS ↦ ?_⟩
  rw [GrothendieckTopology.mem_over_iff] at hS
  refine J.superset_covering (fun Y g hg ↦ ?_) hS
  have h := (Sieve.overEquiv_iff S g).mp hg
  have heq : (Over.homMk (𝟙 Y) (hT.hom_ext _ _) :
        (Over.equivalenceOfIsTerminal hT).inverse.obj Y ⟶
          Over.mk (g ≫ ((Over.equivalenceOfIsTerminal hT).inverse.obj U).hom)) ≫
        (Over.homMk g (hT.hom_ext _ _) :
          Over.mk (g ≫ ((Over.equivalenceOfIsTerminal hT).inverse.obj U).hom) ⟶
            (Over.equivalenceOfIsTerminal hT).inverse.obj U) =
      (Over.equivalenceOfIsTerminal hT).inverse.map g :=
    Over.OverMorphism.ext (Category.id_comp g)
  show S.arrows ((Over.equivalenceOfIsTerminal hT).inverse.map g)
  rw [← heq]
  exact S.downward_closed h _

/-- Sheafification transfers from the localization of a site at a final object to the site
itself, because the two are equivalent as sites. This is the weak-sheafification analogue of
`CategoryTheory.Equivalence.hasSheafify`, which needs the stronger `HasSheafify`. -/
public lemma hasWeakSheafify_of_overTerminal
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (T : C) (hT : Limits.IsTerminal T) {A : Type w} [Category A]
    [HasWeakSheafify (J.over T) A] : HasWeakSheafify J A := by
  let e : C ≌ Over T := (Over.equivalenceOfIsTerminal hT).symm
  let K := J.over T
  have : e.functor.IsCocontinuous J K := isCocontinuous_equivalenceOfIsTerminal J hT
  have : e.inverse.IsCocontinuous K J := by
    show (Over.forget T).IsCocontinuous (J.over T) J
    infer_instance
  have : e.inverse.IsDenseSubsite K J :=
    Equivalence.isDenseSubsite_inverse_of_isCocontinuous J K e
  let L := e.op.congrLeft.functor ⋙ presheafToSheaf K A ⋙ (e.sheafCongr J K A).inverse
  let n : (e.sheafCongr J K A).functor ⋙ sheafToPresheaf K A ⋙
      e.op.congrLeft.inverse ≅ sheafToPresheaf J A := by
    refine NatIso.ofComponents
      (fun F ↦ (e.op.congrLeft.unitIso.app F.obj).symm) (fun {F G} f ↦ ?_)
    show ((e.op.congrLeft.functor ⋙ e.op.congrLeft.inverse).map f.hom) ≫
      (e.op.congrLeft.unitIso.app G.obj).symm.hom =
      (e.op.congrLeft.unitIso.app F.obj).symm.hom ≫ f.hom
    exact e.op.congrLeft.unitIso.inv.naturality f.hom
  have adj : L ⊣ sheafToPresheaf J A :=
    ((e.op.congrLeft.toAdjunction.comp (sheafificationAdjunction K A)).comp
      (e.sheafCongr J K A).symm.toAdjunction).ofNatIsoRight n
  exact ⟨L, ⟨adj⟩⟩

/-- The small étale site of an object of a big étale site has binary products: it has fibre
products and a final object. -/
private lemma hasBinaryProducts_smallEtale (B : BigEtaleSite.{u}) (T : B.Scheme) :
    Limits.HasBinaryProducts (SmallEtale B T.obj T.property) := by
  have := hasPullbacks_smallEtale B T.obj T.property
  have := hasTerminal_smallEtale B T.obj T.property
  exact _root_.hasBinaryProducts_of_hasTerminal_and_pullbacks _

/-- **Stacks 0GKB.** Extension of scalars along a homomorphism of Noetherian rings preserves
constructibility of a sheaf of modules on the small étale site. -/
@[stacks 0GKB]
public theorem isConstructibleModuleSheaf_extendScalars
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type r) (S : Type s) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] (f : R →+* S)
    [HasWeakSheafify (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max r s w} S)]
    [∀ (A T : B.Scheme) (g : T ⟶ A),
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{max r s w} R)
        (SmallEtale.topology B A.obj A.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{max r s w} R)]
    [∀ (A T : B.Scheme) (g : T ⟶ A),
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{max r s w} S)
        (SmallEtale.topology B A.obj A.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{max r s w} S)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max r s w} R))
    (hF : IsConstructibleModuleSheaf B X R F) :
    IsConstructibleModuleSheaf B X S
      ((Sheaf.composeAndSheafify (SmallEtale.topology B X.obj X.property)
        (ModuleCat.extendScalars.{r, s, max r s w} f)).obj F) := by
  intro U
  obtain ⟨stratification, hstratification⟩ := hF U
  refine ⟨stratification, fun i ↦ ?_⟩
  let J := SmallEtale.topology B (stratification.piece i).obj
    (stratification.piece i).property
  have : Limits.HasBinaryProducts
      (SmallEtale B (stratification.piece i).obj (stratification.piece i).property) :=
    hasBinaryProducts_smallEtale B (stratification.piece i)
  have : HasWeakSheafify J (ModuleCat.{max r s w} S) :=
    hasWeakSheafify_of_overTerminal J _ (SmallEtale.finalIsTerminal B _ _)
  let G := smallEtaleBaseChange B (stratification.inclusion i)
  let Fᵢ := (G.sheafPullback (ModuleCat.{max r s w} R)
    (SmallEtale.topology B X.obj X.property) J).obj F
  have hᵢ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R J Fᵢ :=
    hstratification i
  exact isFiniteTypeLocallyConstant_of_iso J S
    (sheafPullbackExtendScalarsAppIso G (SmallEtale.topology B X.obj X.property) J R S f F)
    (isFiniteTypeLocallyConstant_extendScalars J R S f Fᵢ hᵢ)

end AlgebraicGeometry.SmallEtale

end
