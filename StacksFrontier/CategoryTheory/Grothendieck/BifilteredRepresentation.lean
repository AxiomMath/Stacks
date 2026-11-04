module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import StacksCore.Algebra.Homology.QuasiIso
public import StacksCore.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.FilteredComplex.KInjectiveResolution
public import StacksFrontier.Homology.Injectives.FilteredComplex.InverseSystemRepresentation
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Injectives.FilteredComplex.InverseSystemRepresentation

/-!
# Representing two derived inverse systems by one bi-filtered complex

Let `A` be a Grothendieck abelian category, `E` an object of the unbounded derived category
`D(A)`, and let `F, F' : ℤᵒᵖ ⥤ D(A)` be two inverse systems of objects of `D(A)`, each equipped
with a compatible family of maps to the constant system at `E`. Stacks 0ESK says that both
systems can be realized simultaneously by *one* cochain complex carrying *two* filtrations.

The proof is the one in the source. Stacks 0ESJ realizes each system separately by a filtered
complex; Stacks 0BKI replaces the first of those by a filtered K-injective resolution, so that
the comparison isomorphism between its underlying complex and `E` is induced by an honest map of
complexes. The second filtered complex is then mapped into the biproduct of that K-injective
complex with an acyclic complex of injectives — a K-injective resolution of the cone on an
identity — which makes the map a monomorphism without changing the class in `D(A)`, and both
filtrations are pushed forward along the respective monomorphisms into that one complex.

## Main results

* `Stacks.Injectives.exists_bifilteredComplex_representation` (Stacks 0ESK): the bi-filtered
  complex, the identification of its underlying complex with `E`, the two identifications of its
  filtration diagrams with `F` and `F'`, and the two compatibilities with the maps to `E`.

## Implementation notes

A bi-filtered complex is recorded as a `CochainComplex.Filtered` together with a second
`Filtration` of its underlying complex, rather than as a new structure. The two natural
isomorphisms carry all transition maps of the inverse systems, and the two displayed equations
record the compatibility with the maps to `E`.

The acyclic auxiliary complex is needed only to make the second comparison map a monomorphism:
pushing a filtration forward along a map of complexes produces the image filtration, and that
represents the original filtration steps in `D(A)` exactly when the map is monic, since the
pushforward comparison maps are then isomorphisms.

## References

* [Stacks Project, Tag 0ESK](https://stacks.math.columbia.edu/tag/0ESK)
* [Stacks Project, Tag 0ESJ](https://stacks.math.columbia.edu/tag/0ESJ)
* [Stacks Project, Tag 0BKI](https://stacks.math.columbia.edu/tag/0BKI)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe w w' v u

namespace Stacks.Injectives

/-- Every map in the derived category into the image of a K-injective complex is induced by an
honest map of cochain complexes. -/
private lemma exists_map_realizing_iso {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w'} A] (X Y : CochainComplex A ℤ) (hY : Y.IsKInjective)
    (α : DerivedCategory.Q.obj X ≅ DerivedCategory.Q.obj Y) :
    ∃ f : X ⟶ Y, DerivedCategory.Q.map f = α.hom := by
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let e := DerivedCategory.quotientCompQhIso A
  let target := (e.hom.app X) ≫ α.hom ≫ (e.inv.app Y)
  let : Y.IsKInjective := hY
  obtain ⟨g, hg⟩ :=
    (CochainComplex.IsKInjective.Qh_map_bijective (q.obj X) Y).surjective target
  obtain ⟨f, hf⟩ := q.map_surjective g
  refine ⟨f, ?_⟩
  apply (cancel_epi (e.hom.app X)).1
  calc
    e.hom.app X ≫ DerivedCategory.Q.map f =
        DerivedCategory.Qh.map (q.map f) ≫ e.hom.app Y :=
          (DerivedCategory.quotientCompQhIso_hom_naturality f).symm
    _ = target ≫ e.hom.app Y := by rw [hf, hg]
    _ = e.hom.app X ≫ α.hom := by simp [target]



/-- Adding a complex that vanishes in the derived category does not change the derived class. -/
private noncomputable def mapBiprodLeftIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w'} A]
    (X Y : CochainComplex A ℤ)
    (hY : IsZero (DerivedCategory.Q.obj Y)) :
    DerivedCategory.Q.obj (X ⊞ Y) ≅ DerivedCategory.Q.obj X := by
  let F := DerivedCategory.Q (C := A)
  let : Functor.Additive F := inferInstance
  refine ⟨F.map (biprod.fst (X := X) (Y := Y)),
    F.map (biprod.inl (X := X) (Y := Y)), ?_, ?_⟩
  · have hzero : F.map (biprod.snd (X := X) (Y := Y)) = 0 := hY.eq_of_tgt _ _
    have htotal := congrArg F.map (biprod.total (X := X) (Y := Y))
    change F.map (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) =
      F.map (𝟙 (X ⊞ Y)) at htotal
    rw [Functor.map_add, Functor.map_comp, Functor.map_comp, hzero, zero_comp,
      add_zero] at htotal
    simpa using htotal
  · rw [← Functor.map_comp, biprod.inl_fst, F.map_id]

/-- A natural transformation of inverse systems of complexes whose components become
isomorphisms in the derived category induces an isomorphism of the derived diagrams. -/
private noncomputable def inverseMapNatIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w'} A]
    {F G : ℤᵒᵖ ⥤ CochainComplex A ℤ}
    (α : F ⟶ G) (hα : ∀ i, IsIso (DerivedCategory.Q.map (α.app i))) :
    G ⋙ DerivedCategory.Q ≅ F ⋙ DerivedCategory.Q := by
  refine NatIso.ofComponents (fun i => (asIso (DerivedCategory.Q.map (α.app i))).symm) ?_
  intro i j f
  let := hα i
  let := hα j
  have hn : DerivedCategory.Q.map (α.app i) ≫ DerivedCategory.Q.map (G.map f) =
      DerivedCategory.Q.map (F.map f) ≫ DerivedCategory.Q.map (α.app j) := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    exact congrArg (fun h => DerivedCategory.Q.map h) (α.naturality f).symm
  calc
    DerivedCategory.Q.map (G.map f) ≫ inv (DerivedCategory.Q.map (α.app j)) =
        inv (DerivedCategory.Q.map (α.app i)) ≫
          (DerivedCategory.Q.map (α.app i) ≫ DerivedCategory.Q.map (G.map f)) ≫
            inv (DerivedCategory.Q.map (α.app j)) := by simp [Category.assoc]
    _ = inv (DerivedCategory.Q.map (α.app i)) ≫
          (DerivedCategory.Q.map (F.map f) ≫ DerivedCategory.Q.map (α.app j)) ≫
            inv (DerivedCategory.Q.map (α.app j)) := by rw [hn]
    _ = inv (DerivedCategory.Q.map (α.app i)) ≫ DerivedCategory.Q.map (F.map f) := by
          simp [Category.assoc]

/-- Pushing a filtration forward along a monomorphism is an isomorphism on each filtration
step: the comparison map is monic and epic, hence invertible. -/
private lemma pushforwardLevel_isIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w'} A]
    (S : CochainComplex.Filtered A) {P : CochainComplex A ℤ}
    (g : S.X ⟶ P) [Mono g] (i : ℤᵒᵖ) :
    IsIso (DerivedCategory.Q.map
      ((FilteredObject.pushforwardHom S g).natTrans.app i)) := by
  have : Mono ((FilteredObject.pushforwardHom S g).natTrans.app i) := by
    show Mono (factorThruImage (S.filtration.ι.app i ≫ g))
    exact mono_of_mono_fac (image.fac _)
  have : Epi ((FilteredObject.pushforwardHom S g).natTrans.app i) := by
    show Epi (factorThruImage (S.filtration.ι.app i ≫ g))
    infer_instance
  have := isIso_of_mono_of_epi ((FilteredObject.pushforwardHom S g).natTrans.app i)
  exact Functor.map_isIso _ _

/-- The filtration inclusions of the pushforward filtration, expressed through the original
filtration inclusions and the pushforward comparison. -/
private lemma pushforward_inclusion_map
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w'} A]
    (S : CochainComplex.Filtered A) {P : CochainComplex A ℤ}
    (g : S.X ⟶ P) [Mono g] (i : ℤᵒᵖ)
    [IsIso (DerivedCategory.Q.map
      ((FilteredObject.pushforwardHom S g).natTrans.app i))] :
    DerivedCategory.Q.map
        ((FilteredObject.pushforwardObj S g).filtration.ι.app i) =
      inv (DerivedCategory.Q.map
        ((FilteredObject.pushforwardHom S g).natTrans.app i)) ≫
        DerivedCategory.Q.map (S.filtration.ι.app i) ≫
          DerivedCategory.Q.map (FilteredObject.pushforwardHom S g).hom := by
  rw [IsIso.eq_inv_comp, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg DerivedCategory.Q.map ((FilteredObject.pushforwardHom S g).comm i)

/-- Pushing a filtration forward along a monomorphism does not change its derived filtration
diagram. -/
private noncomputable def imageFiltrationDiagramIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w'} A]
    (S : CochainComplex.Filtered A) {P : CochainComplex A ℤ} (g : S.X ⟶ P) [Mono g] :
      (FilteredObject.pushforwardObj S g).filtration.diagram ⋙ DerivedCategory.Q ≅
      S.filtration.diagram ⋙ DerivedCategory.Q := by
  let t := FilteredObject.pushforwardHom S g
  have hlevel (i : ℤᵒᵖ) : IsIso (DerivedCategory.Q.map (t.natTrans.app i)) :=
    pushforwardLevel_isIso S g i
  exact inverseMapNatIso t.natTrans hlevel

/-- Compatibility of the pushforward filtration with a map to `E`, given compatibility of the
original filtration and of the monomorphism. -/
private lemma pushforward_inclusion_comp
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w'} A]
    (S : CochainComplex.Filtered A) {P : CochainComplex A ℤ} (g : S.X ⟶ P) [Mono g]
    {E : DerivedCategory A} (eS : DerivedCategory.Q.obj S.X ≅ E)
    (eP : DerivedCategory.Q.obj P ≅ E) (hg : DerivedCategory.Q.map g ≫ eP.hom = eS.hom)
    {F : ℤᵒᵖ ⥤ DerivedCategory A} (η : S.filtration.diagram ⋙ DerivedCategory.Q ≅ F)
    (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    (h : ∀ i : ℤᵒᵖ, DerivedCategory.Q.map (S.filtration.ι.app i) ≫ eS.hom =
      η.hom.app i ≫ φ.app i) (i : ℤᵒᵖ) :
    DerivedCategory.Q.map ((FilteredObject.pushforwardObj S g).filtration.ι.app i) ≫ eP.hom =
      (imageFiltrationDiagramIso S g ≪≫ η).hom.app i ≫ φ.app i := by
  have := pushforwardLevel_isIso S g i
  have hg' : DerivedCategory.Q.map (FilteredObject.pushforwardHom S g).hom ≫ eP.hom =
    eS.hom := hg
  rw [pushforward_inclusion_map S g i, Category.assoc, Category.assoc, hg', ← Category.assoc,
    Category.assoc, h i]
  exact (Category.assoc _ _ _).symm

variable {A : Type u} [Category.{v} A] [Abelian A]
  [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w'} A]

/-- **Stacks 0ESK.** Two inverse systems of objects of the derived category of a Grothendieck
abelian category, each with a compatible family of maps to one object `E`, can be represented by
two filtrations of a single cochain complex. -/
@[stacks 0ESK]
theorem exists_bifilteredComplex_representation
    (E : DerivedCategory A)
    (F F' : ℤᵒᵖ ⥤ DerivedCategory A)
    (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    (φ' : F' ⟶ (Functor.const ℤᵒᵖ).obj E) :
    ∃ (K : CochainComplex.Filtered A)
      (filtration' : Filtration K.X ℤᵒᵖ)
      (e : DerivedCategory.Q.obj K.X ≅ E)
      (η : K.filtration.diagram ⋙ DerivedCategory.Q ≅ F)
      (η' : filtration'.diagram ⋙ DerivedCategory.Q ≅ F'),
      (∀ i : ℤᵒᵖ,
        DerivedCategory.Q.map (K.filtration.ι.app i) ≫ e.hom =
          η.hom.app i ≫ φ.app i) ∧
      (∀ i : ℤᵒᵖ,
        DerivedCategory.Q.map (filtration'.ι.app i) ≫ e.hom =
          η'.hom.app i ≫ φ'.app i) := by
  classical
  obtain ⟨K₀, e₀, η₀, h₀⟩ := exists_filteredComplex_representation E F φ
  obtain ⟨J, j, _, _, _, _, hJkinj, _, _, _, qj, qfil, _, _⟩ :=
    exists_filtered_quasiIso_isKInjective.{w} K₀
  obtain ⟨L, eL, ηL, hL⟩ := exists_filteredComplex_representation E F' φ'
  let : QuasiIso j.hom := qj
  have hqfil (i : ℤᵒᵖ) : IsIso (DerivedCategory.Q.map (j.natTrans.app i)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (qfil i.unop)
  let τJ := inverseMapNatIso j.natTrans hqfil
  let eJ : DerivedCategory.Q.obj J.X ≅ E := (asIso (DerivedCategory.Q.map j.hom)).symm ≪≫ e₀
  let ηJ : J.filtration.diagram ⋙ DerivedCategory.Q ≅ F := τJ ≪≫ η₀
  have hJ (i : ℤᵒᵖ) :
      DerivedCategory.Q.map (J.filtration.ι.app i) ≫ eJ.hom =
        ηJ.hom.app i ≫ φ.app i := by
    have hlevel :
        DerivedCategory.Q.map (J.filtration.ι.app i) ≫ inv (DerivedCategory.Q.map j.hom) =
          inv (DerivedCategory.Q.map (j.natTrans.app i)) ≫
            DerivedCategory.Q.map (K₀.filtration.ι.app i) := by
      apply (cancel_mono (DerivedCategory.Q.map j.hom)).1
      have hcomm : DerivedCategory.Q.map (K₀.filtration.ι.app i) ≫
          DerivedCategory.Q.map j.hom =
        DerivedCategory.Q.map (j.natTrans.app i) ≫
          DerivedCategory.Q.map (J.filtration.ι.app i) := by
        rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
        exact (congrArg (fun f => DerivedCategory.Q.map f) (j.comm i)).symm
      calc
        (DerivedCategory.Q.map (J.filtration.ι.app i) ≫ inv (DerivedCategory.Q.map j.hom)) ≫
            DerivedCategory.Q.map j.hom = DerivedCategory.Q.map (J.filtration.ι.app i) := by simp
        _ = inv (DerivedCategory.Q.map (j.natTrans.app i)) ≫
            (DerivedCategory.Q.map (j.natTrans.app i) ≫
              DerivedCategory.Q.map (J.filtration.ι.app i)) := by simp
        _ = inv (DerivedCategory.Q.map (j.natTrans.app i)) ≫
            (DerivedCategory.Q.map (K₀.filtration.ι.app i) ≫
              DerivedCategory.Q.map j.hom) := by rw [hcomm.symm]
        _ = (inv (DerivedCategory.Q.map (j.natTrans.app i)) ≫
            DerivedCategory.Q.map (K₀.filtration.ι.app i)) ≫
              DerivedCategory.Q.map j.hom := by simp [Category.assoc]
    dsimp [eJ, ηJ, τJ]
    calc
      DerivedCategory.Q.map (J.filtration.ι.app i) ≫
          inv (DerivedCategory.Q.map j.hom) ≫ e₀.hom =
          inv (DerivedCategory.Q.map (j.natTrans.app i)) ≫
            DerivedCategory.Q.map (K₀.filtration.ι.app i) ≫ e₀.hom := by
              simpa [Category.assoc] using congrArg (fun h => h ≫ e₀.hom) hlevel
      _ = inv (DerivedCategory.Q.map (j.natTrans.app i)) ≫
          (DerivedCategory.Q.map (K₀.filtration.ι.app i) ≫ e₀.hom) := by simp
      _ = inv (DerivedCategory.Q.map (j.natTrans.app i)) ≫
          (η₀.hom.app i ≫ φ.app i) := by rw [h₀ i]
      _ = ηJ.hom.app i ≫ φ.app i := by
        show inv (DerivedCategory.Q.map (j.natTrans.app i)) ≫
          (η₀.hom.app i ≫ φ.app i) =
          (inv (DerivedCategory.Q.map (j.natTrans.app i)) ≫ η₀.hom.app i) ≫ φ.app i
        simp [Category.assoc]
  let C := CochainComplex.mappingCone (𝟙 L.X)
  let I := (kInjectiveResolutionFunctor A).obj C
  let r := (kInjectiveResolutionInclusion A).app C
  have hC : C.Acyclic := mappingCone_id_acyclic L.X
  have hr : QuasiIso r := by dsimp [r]; infer_instance
  have hIac : I.Acyclic := by
    rw [HomologicalComplex.acyclic_iff_isZero_homology]
    intro n
    have hsrc := (HomologicalComplex.acyclic_iff_isZero_homology C).1 hC n
    have hmap : IsIso (HomologicalComplex.homologyMap r n) := by infer_instance
    exact hsrc.of_iso (asIso (HomologicalComplex.homologyMap r n)).symm
  let g : L.X ⟶ I := CochainComplex.mappingCone.inr (𝟙 L.X) ≫ r
  let P := J.X ⊞ I
  let jP : J.X ⟶ P := biprod.inl
  let f := Classical.choose (exists_map_realizing_iso L.X J.X hJkinj (eL ≪≫ eJ.symm))
  let m : L.X ⟶ P := biprod.lift f g
  have hm : Mono m := HomologicalComplex.mono_of_mono_f m (fun n => by
    have : Mono ((CochainComplex.mappingCone.inr (𝟙 L.X)).f n) :=
      mono_of_mono_fac (CochainComplex.mappingCone.inr_f_snd_v (𝟙 L.X) n)
    have hgn : Mono (g.f n) := by
      show Mono ((CochainComplex.mappingCone.inr (𝟙 L.X)).f n ≫ r.f n)
      infer_instance
    exact mono_of_mono_fac (show m.f n ≫ (biprod.snd : P ⟶ I).f n = g.f n by simp [m]))
  have hIzero : IsZero (DerivedCategory.Q.obj I) := isZero_Q_obj_of_acyclic I hIac
  let qbp := mapBiprodLeftIso J.X I hIzero
  let eP : DerivedCategory.Q.obj P ≅ E := qbp ≪≫ eJ
  have hjP : DerivedCategory.Q.map jP ≫ eP.hom = eJ.hom := by
    have hmap : DerivedCategory.Q.map jP ≫ qbp.hom = 𝟙 _ := by
      show DerivedCategory.Q.map (biprod.inl (X := J.X) (Y := I)) ≫
        DerivedCategory.Q.map (biprod.fst (X := J.X) (Y := I)) = _
      exact (mapBiprodLeftIso J.X I hIzero).inv_hom_id
    dsimp [eP]
    calc
      DerivedCategory.Q.map jP ≫ qbp.hom ≫ eJ.hom =
          (DerivedCategory.Q.map jP ≫ qbp.hom) ≫ eJ.hom := by simp [Category.assoc]
      _ = eJ.hom := by rw [hmap]; simp
  have hmrep : DerivedCategory.Q.map m ≫ eP.hom = eL.hom := by
    have hf : DerivedCategory.Q.map f = (eL ≪≫ eJ.symm).hom :=
      Classical.choose_spec (exists_map_realizing_iso L.X J.X hJkinj (eL ≪≫ eJ.symm))
    have hmap : DerivedCategory.Q.map m ≫ qbp.hom = DerivedCategory.Q.map f := by
      show DerivedCategory.Q.map (biprod.lift f g) ≫
        DerivedCategory.Q.map (biprod.fst (X := J.X) (Y := I)) = _
      rw [← DerivedCategory.Q.map_comp]
      simp [biprod.lift_fst]
    dsimp [eP]
    calc
      DerivedCategory.Q.map m ≫ qbp.hom ≫ eJ.hom =
          (DerivedCategory.Q.map m ≫ qbp.hom) ≫ eJ.hom := by simp [Category.assoc]
      _ = eL.hom := by rw [hmap, hf]; simp [eJ, Category.assoc]
  let K : CochainComplex.Filtered A := FilteredObject.pushforwardObj J jP
  let filtration' : Filtration P ℤᵒᵖ := (FilteredObject.pushforwardObj L m).filtration
  let η : K.filtration.diagram ⋙ DerivedCategory.Q ≅ F :=
    imageFiltrationDiagramIso J jP ≪≫ ηJ
  let η' : filtration'.diagram ⋙ DerivedCategory.Q ≅ F' :=
    imageFiltrationDiagramIso L m ≪≫ ηL
  refine ⟨K, filtration', eP, η, η', ?_, ?_⟩
  · exact pushforward_inclusion_comp J jP eJ eP hjP ηJ φ hJ
  · exact pushforward_inclusion_comp L m eL eP hmrep ηL φ' hL

end Stacks.Injectives

end
