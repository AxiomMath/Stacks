module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemCohomology
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SingleDeligneSystem
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.FiniteTypeExtension
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphismSymm

/-!
# Images of Deligne systems under a triangulated functor

Let `j : U ⟶ X` and `j' : V ⟶ Y` be open immersions of Noetherian schemes and
`R : D^b_{Coh}(𝒪_X) ⥤ D^b_{Coh}(𝒪_Y)` a triangulated functor. Whether the image under `R` of a
Deligne system along `j` is pro-isomorphic to a Deligne system along `j'` depends only on the value
of the Deligne system. As a property of that value it satisfies two out of three along
distinguished triangles of `D^b_{Coh}(𝒪_U)`, by [Stacks, Tag 0G4M] and [Stacks, Tag 0G4Q], and
hence, along the truncation triangles, it reduces to the case of a coherent module placed in one
degree, and then, a coherent module on `U` extending to `X`, to the Deligne systems `(𝓘^n𝓕[-p])`
of coherent `𝒪_X`-modules. This is the reduction in the first proof of [Stacks, Tag 0G4W].

## Main results

* `AlgebraicGeometry.proIsoDeligneSystem_values_comp_iff`: only the value matters.
* `AlgebraicGeometry.proIsoDeligneSystem_values_comp_π₂`: two out of three.
* `AlgebraicGeometry.proIsoDeligneSystem_values_comp_of_truncGELE`: reduction to one degree.
* `AlgebraicGeometry.proIsoDeligneSystem_values_comp_of_single`: reduction to coherent modules
  on `X`.

## References

* [Stacks Project, Tag 0G4W](https://stacks.math.columbia.edu/tag/0G4W)
* [Stacks Project, Tag 0G4M](https://stacks.math.columbia.edu/tag/0G4M)
* [Stacks Project, Tag 0G4Q](https://stacks.math.columbia.edu/tag/0G4Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance] CategoryTheory.uliftCategory
attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

section Transfer

variable {U X Y V : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j] [IsNoetherian X]
  {j' : V ⟶ Y} [IsOpenImmersion j'] [IsNoetherian Y]
  (R : BoundedCoherentDerived X ⥤ BoundedCoherentDerived Y)

omit [IsNoetherian X] in
/-- If two inverse systems have isomorphic pro-objects and the image of one under a functor `R`
is pro-isomorphic to a Deligne system, so is the image of the other. -/
public lemma proIsoDeligneSystem_comp_of_iso {F G : ℕᵒᵖ ⥤ BoundedCoherentDerived X}
    (e : ProSeq.of F ≅ ProSeq.of G) (h : ProIsoDeligneSystem j' (G ⋙ R)) :
    ProIsoDeligneSystem j' (F ⋙ R) := by
  obtain ⟨D, ⟨i⟩⟩ := h
  exact ⟨D, ⟨ProSeq.isoOfProIso (Pro.proIsoWhiskerRight (ProSeq.proIsoOfIso e) R) ≪≫ i⟩⟩

variable (j) in
/-- The pro-object of the assigned Deligne system of `K` is that of any Deligne system with value
`K`: both are `Rj_! K`. -/
public def valuesProObjectIso (D : DeligneSystem j) (W : D.Value) :
    ProSeq.of ((DeligneSystem.values j).system W.obj) ≅ D.proObject :=
  (extensionByZeroIso (restrictBoundedCoherentLift j)
    (DeligneSystem.values j).toAssignment W.obj).symm ≪≫ W.extensionByZeroIso.symm

variable (j) in
/-- Isomorphic objects of `D^b_{Coh}(𝒪_U)` have isomorphic assigned Deligne systems, as
pro-objects. -/
public def valuesProObjectIsoOfIso {K K' : BoundedCoherentDerived U} (e : K ≅ K') :
    ProSeq.of ((DeligneSystem.values j).system K) ≅
      ProSeq.of ((DeligneSystem.values j).system K') :=
  (extensionByZeroIso (restrictBoundedCoherentLift j)
    (DeligneSystem.values j).toAssignment K).symm ≪≫ (extensionByZeroOpenImmersion j).mapIso e ≪≫
    extensionByZeroIso (restrictBoundedCoherentLift j) (DeligneSystem.values j).toAssignment K'

/-- The image of the assigned system of `K` under `R` is pro-isomorphic to a Deligne system if and
only if that of any Deligne system with value `K` is. -/
public lemma proIsoDeligneSystem_values_comp_iff (D : DeligneSystem j) (W : D.Value) :
    ProIsoDeligneSystem j' ((DeligneSystem.values j).system W.obj ⋙ R) ↔
      ProIsoDeligneSystem j' (D.system ⋙ R) :=
  ⟨proIsoDeligneSystem_comp_of_iso R (valuesProObjectIso j D W).symm,
    proIsoDeligneSystem_comp_of_iso R (valuesProObjectIso j D W)⟩

/-- The vertices of the image of a system of triangles under a functor `R` are the images of its
vertices. -/
public def mapTriangleCompπ₁Iso (T : ℕᵒᵖ ⥤ Triangle (BoundedCoherentDerived X))
    [R.CommShift ℤ] : (T ⋙ R.mapTriangle) ⋙ Triangle.π₁ ≅ (T ⋙ Triangle.π₁) ⋙ R :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The vertices of the image of a system of triangles under a functor `R` are the images of its
vertices. -/
public def mapTriangleCompπ₂Iso (T : ℕᵒᵖ ⥤ Triangle (BoundedCoherentDerived X))
    [R.CommShift ℤ] : (T ⋙ R.mapTriangle) ⋙ Triangle.π₂ ≅ (T ⋙ Triangle.π₂) ⋙ R :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The vertices of the image of a system of triangles under a functor `R` are the images of its
vertices. -/
public def mapTriangleCompπ₃Iso (T : ℕᵒᵖ ⥤ Triangle (BoundedCoherentDerived X))
    [R.CommShift ℤ] : (T ⋙ R.mapTriangle) ⋙ Triangle.π₃ ≅ (T ⋙ Triangle.π₃) ⋙ R :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

variable [R.CommShift ℤ] [R.IsTriangulated]

/-- A vertex of a system of triangles over a distinguished triangle of `D^b_{Coh}(𝒪_U)`, which
is a Deligne system, has as value the corresponding vertex of that triangle. -/
public def vertexValue (T : Triangle (BoundedCoherentDerived U))
    (TX : ℕᵒᵖ ⥤ Triangle (BoundedCoherentDerived X))
    (eR : TX ⋙ (restrictBoundedCoherentLift j).mapTriangle ≅ (Functor.const ℕᵒᵖ).obj T)
    (π : Triangle (BoundedCoherentDerived U) ⥤ BoundedCoherentDerived U)
    (π' : Triangle (BoundedCoherentDerived X) ⥤ BoundedCoherentDerived X)
    (w : π' ⋙ restrictBoundedCoherentLift j ≅ (restrictBoundedCoherentLift j).mapTriangle ⋙ π)
    (D : DeligneSystem j) (eD : TX ⋙ π' ≅ D.system) : D.Value :=
  D.valueOfIso (π.obj T)
    (Functor.isoWhiskerRight eD.symm (restrictBoundedCoherent j) ≪≫
      Functor.isoWhiskerRight
        (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft TX w ≪≫
          (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eR π ≪≫
          Functor.constComp _ _ _) (boundedCoherentDerived U).ι ≪≫
      Functor.constComp _ _ _)

/-- **Two out of three for the pushforward of Deligne systems.** For a triangulated functor
`R : D^b_{Coh}(𝒪_X) ⥤ D^b_{Coh}(𝒪_Y)` and a distinguished triangle `K ⟶ L ⟶ M ⟶ K[1]` of
`D^b_{Coh}(𝒪_U)`, if the images under `R` of the Deligne systems of `K` and of `M` are
pro-isomorphic to Deligne systems along `j'`, then so is that of `L`. This is [Stacks, Tag 0G4M]
followed by [Stacks, Tag 0G4Q]. -/
public theorem proIsoDeligneSystem_values_comp_π₂ (T : Triangle (BoundedCoherentDerived U))
    (hT : T ∈ distTriang (BoundedCoherentDerived U))
    (h₁ : ProIsoDeligneSystem j' ((DeligneSystem.values j).system T.obj₁ ⋙ R))
    (h₃ : ProIsoDeligneSystem j' ((DeligneSystem.values j).system T.obj₃ ⋙ R)) :
    ProIsoDeligneSystem j' ((DeligneSystem.values j).system T.obj₂ ⋙ R) := by
  obtain ⟨DK, DL, DM, TX, hTX, ⟨eK⟩, ⟨eL⟩, ⟨eM⟩, ⟨eR⟩⟩ :=
    DeligneTriangle.exists_deligneSystem_distTriang_boundedCoherent j T hT
  let WK := vertexValue T TX eR Triangle.π₁ Triangle.π₁ (Iso.refl _) DK eK
  let WL := vertexValue T TX eR Triangle.π₂ Triangle.π₂ (Iso.refl _) DL eL
  let WM := vertexValue T TX eR Triangle.π₃ Triangle.π₃ (Iso.refl _) DM eM
  replace h₁ := (proIsoDeligneSystem_values_comp_iff R DK WK).mp h₁
  replace h₃ := (proIsoDeligneSystem_values_comp_iff R DM WM).mp h₃
  refine (proIsoDeligneSystem_values_comp_iff R DL WL).mpr ?_
  have h₁' : ProIsoDeligneSystem j' ((TX ⋙ R.mapTriangle) ⋙ Triangle.π₁) :=
    ProIsoDeligneSystem.of_natIso
      (mapTriangleCompπ₁Iso R TX ≪≫ Functor.isoWhiskerRight eK R) h₁
  have h₃' : ProIsoDeligneSystem j' ((TX ⋙ R.mapTriangle) ⋙ Triangle.π₃) :=
    ProIsoDeligneSystem.of_natIso
      (mapTriangleCompπ₃Iso R TX ≪≫ Functor.isoWhiskerRight eM R) h₃
  have h₂' := DeligneSystem.proIsoDeligneSystem_π₂ (TX ⋙ R.mapTriangle)
    (fun n => R.map_distinguished _ (hTX n)) h₁' h₃'
  exact ProIsoDeligneSystem.of_natIso
    (Functor.isoWhiskerRight eL R).symm h₂'

/-- **The reduction to a coherent module in one degree.** For a triangulated functor `R`, if the
images under `R` of the Deligne systems of the objects of `D^b_{Coh}(𝒪_U)` concentrated in a
single degree are pro-isomorphic to Deligne systems along `j'`, then so are those of all
objects. This is the induction along the truncation triangles of the source. -/
public theorem proIsoDeligneSystem_values_comp_of_truncGELE
    (H : ∀ (K : BoundedCoherentDerived U) (p : ℤ),
      ProIsoDeligneSystem j' ((DeligneSystem.values j).system
        ((boundedCoherentTStructure U).truncGELE p p |>.obj K) ⋙ R))
    (K : BoundedCoherentDerived U) :
    ProIsoDeligneSystem j' ((DeligneSystem.values j).system K ⋙ R) := by
  let P : (ℕᵒᵖ ⥤ BoundedCoherentDerived U) → Prop := fun F =>
    ProIsoDeligneSystem j' ((DeligneSystem.values j).system (F.obj (op 0)) ⋙ R)
  obtain ⟨a, b, ha, hb⟩ := exists_isGE_isLE_boundedCoherentTStructure K
  change P ((Functor.const ℕᵒᵖ).obj K)
  rcases le_or_gt a b with hab | hab
  · refine (boundedCoherentTStructure U).prop_of_truncGELE P (fun e h => ?_)
      (fun T hT h₁ h₃ => proIsoDeligneSystem_values_comp_π₂ R (T.obj (op 0)) (hT _) h₁ h₃)
      hab _ (fun _ => ha) (fun _ => hb) (fun p _ _ => H K p)
    exact proIsoDeligneSystem_comp_of_iso R (valuesProObjectIsoOfIso j (e.app (op 0))) h
  · have hz : IsZero K := (boundedCoherentTStructure U).isZero K b a hab
    have hz' : IsZero ((boundedCoherentTStructure U).truncGELE a a |>.obj K) :=
      ((boundedCoherentTStructure U).truncGELE a a).map_isZero hz
    exact proIsoDeligneSystem_comp_of_iso R
      (valuesProObjectIsoOfIso j (hz.iso hz')) (H K a)

end Transfer

section Single

variable {X Y V : Scheme.{u}} [IsNoetherian X] (W : X.Opens)
  {j' : V ⟶ Y} [IsOpenImmersion j'] [IsNoetherian Y]
  (R : BoundedCoherentDerived X ⥤ BoundedCoherentDerived Y)

/-- **Reduction to a coherent module on `X`.** If, for every coherent `𝒪_X`-module `𝓕` and every
`p`, the image under `R` of the Deligne system `(𝓘^n𝓕[-p])` is pro-isomorphic to a Deligne system
along `j'`, then so is the image of the Deligne system of every object of `D^b_{Coh}(𝒪_U)`
concentrated in one degree: such an object is a coherent `𝒪_U`-module placed in that degree,
which extends to a coherent `𝒪_X`-module ([Stacks, Tag 01PI]). -/
public theorem proIsoDeligneSystem_values_comp_of_single (I : X.IdealSheafData)
    (hI : (I.support : Set X) = (Set.range W.ι.base)ᶜ)
    (H : ∀ (F : X.Modules) [F.IsCoherent] (p : ℤ),
      ProIsoDeligneSystem j' ((singleDeligneSystem W I hI F p).system ⋙ R))
    (K : BoundedCoherentDerived W) (p : ℤ) :
    ProIsoDeligneSystem j' ((DeligneSystem.values W.ι).system
      ((boundedCoherentTStructure W).truncGELE p p |>.obj K) ⋙ R) := by
  set K' := (boundedCoherentTStructure W).truncGELE p p |>.obj K
  have hGE : K'.obj.IsGE p :=
    ((ObjectProperty.tStructure_isGE_iff (boundedCoherentDerived W)
      DerivedCategory.TStructure.t K' p).mp
        (inferInstanceAs ((boundedCoherentTStructure W).IsGE K' p)))
  have hLE : K'.obj.IsLE p :=
    ((ObjectProperty.tStructure_isLE_iff (boundedCoherentDerived W)
      DerivedCategory.TStructure.t K' p).mp
        (inferInstanceAs ((boundedCoherentTStructure W).IsLE K' p)))
  obtain ⟨G, ⟨eG⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K'.obj p
  have hG : G.IsCoherent := by
    have hc : ((DerivedCategory.homologyFunctor W.toScheme.Modules p).obj K'.obj).IsCoherent :=
      K'.property.2 p
    exact (coherentInModules W).prop_of_iso
      ((DerivedCategory.homologyFunctor W.toScheme.Modules p).mapIso eG ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso W.toScheme.Modules p).app G) hc
  have : CompactSpace X := inferInstance
  have : QuasiSeparatedSpace X := NoetherianSpace.to_quasiSeparatedSpace
  obtain ⟨F, hF, ⟨eF⟩⟩ := exists_isCoherent_restrict_iso W
    (TopologicalSpace.NoetherianSpace.isCompact _) G
  have := hF
  let φ : (Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj
      (DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) p).obj F)) ≅
        (boundedCoherentDerived W).ι.obj K' :=
    ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategorySingleFunctor p).app F ≪≫
      (DerivedCategory.singleFunctor W.toScheme.Modules p).mapIso eF ≪≫ eG.symm
  exact (proIsoDeligneSystem_values_comp_iff R (singleDeligneSystem W I hI F p)
    (DeligneSystem.ofComplexValue I hI _ _ _ _ K' φ)).mpr (H F p)

end Single

end AlgebraicGeometry

end
