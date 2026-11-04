module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkAcyclic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkTensorComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Point.ConservativeFamily
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkDerived
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.DerivedComparison
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Tor amplitude is computed at the stalks, on a ringed site

Let `(C, O)` be a ringed site, `E` an object of `D(O)` and `a ≤ b` integers. Stacks 0DJJ says
that Tor amplitude in `[a, b]` passes to the derived stalk `E_Φ` at every point `Φ` of `C`, and
that the converse holds as soon as `C` has enough points.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeCanonical_derivedModuleFiber`:
  **Stacks 0DJJ (1)** for a given derived tensor product datum `T`, Tor amplitude in `[a, b]` of
  `E` implies Tor amplitude in `[a, b]` of `E_Φ` over the stalk ring `O_Φ`, for every point `Φ`.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_forall_derivedModuleFiber`:
  **Stacks 0DJJ (2)** for a given `T`, the converse on a site with a conservative family of
  points.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_forall_derivedModuleFiber_family`:
  the same converse with the hypothesis asked for only at the members of one given conservative
  family of points, rather than at every point of the site.

## Implementation notes

The source proves (1) by viewing the stalk at `Φ` as the pullback along the morphism of ringed
sites `(Φ, O_Φ) → (C, O)` and citing Stacks 08H5, and (2) by testing the vanishing of
`H^i(E ⊗^L_O F)` at stalks and using that stalks commute with the derived tensor product. Both
halves are proved here instead through the flat-representative characterisation of Tor
amplitude, Stacks 08G1 on the sheaf side and Stacks 0654 on the module side, which avoids the
compatibility of the derived tensor product with stalks altogether:

* For (1), a representative `K` of `E` by flat `O`-modules concentrated in `[a, b]` has a
  degreewise stalk `K_Φ` which is a complex of flat `O_Φ`-modules concentrated in `[a, b]` —
  flatness of the stalk of a flat module is Stacks 05VB — and `K_Φ` represents `E_Φ` because the
  stalk functor is exact, so `E_Φ` has Tor amplitude in `[a, b]` by Stacks 0654.
* For (2), the cohomology of `E` is read at the stalks, which bounds it to `[a, b]`; a flat
  resolution `P` of `E` which vanishes above `b` is then truncated at `a`, exactly as in Stacks
  08G1, and the one term that changes, `Coker(d_P^{a-1})`, is flat because each of its stalks is:
  the stalk of that cokernel is the cokernel of `d_{P_Φ}^{a-1}`, which is flat by Stacks 0653
  applied to `P_Φ`. Flatness of a sheaf of modules is detected at the stalks by Stacks 05VC.

Tor amplitude on the sheaf side is measured against a given derived tensor product datum `T`, as
in `Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude`; on the module side it is the
canonical Tor amplitude `StacksDraft.TorAmplitude.HasTorAmplitudeCanonical`, read at the
canonical derived tensor product of `D(O_Φ)`, since `Mod(O_Φ)` is an ordinary module category
and has one. Keeping `T` a parameter is what leaves the sections universe `w` free of the site's
hom universe `v` here; the source's statement, about *the* derived tensor product of the site —
the one Stacks 06YU constructs, where those two universes coincide — is
`StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.StalksCanonical`, which instantiates
`T` and carries the tag.

The derived stalk functor `Stacks.derivedModuleFiber` is stated over
`Stacks.commRingSheafToRingSheaf O`, the underlying sheaf of rings written as
`(sheafCompose J (forget₂ CommRingCat RingCat)).obj O`, whereas `Mod(O)` here is
`AlgebraicGeometry.RingedSite.Modules`, written over `Stacks.SheafOfModules.Tensor.ringSheaf O`.
The two sheaves of rings are equal by `rfl`, so every statement crossing them elaborates; what
does not cross is *instance search*, which works up to reducible unfolding only and so does not
see one spelling when the other is wanted. `HasDerivedCategory` is the class at issue: its hom
universe `d` is free here, and left to instance search the goal
`HasDerivedCategory.{?d} (SheafOfModules (commRingSheafToRingSheaf O))` is closed not by the
ambient hypothesis on `Mod(O)` but by `HasDerivedCategory.standard`, which pins `?d` to the
standard hom universe and yields `D(O)` at the wrong universe — an application type mismatch at
`E`. Each occurrence of the derived stalk therefore names the ambient instance `hd` at the
spelling the stalk API uses. This is the hazard recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteFlat`; migrating the stalk API onto
`Stacks.SheafOfModules.Tensor.ringSheaf` would remove the need for it.

All five universes are independent: the two site universes `u` and `v`, the universe `w` of the
sections of `O` and of the modules — which is also the universe of the points of the site at
which the stalks are taken — and the hom universe `d` of `D(O)`. This used to read `w = max u v`,
a pin inherited from Stacks 08G1, whose converse half rests on the unit law for the ordinary
tensor product; the unit law is now available at a free `w`
(`Stacks.SheafOfModules.sheafTensorUnitNatIsoFreeSections`), and the stalk-side inputs —
Stacks 05VB, 05VC and 04EQ, and the derived stalk functor — were free in `w` already. What is
needed instead is `LocallySmall.{w} Y.C`, which is what makes the stalk at a `w`-point of a
`w`-valued sheaf exist; at `w = max u v` it is an instance, so no existing instantiation
changes. The degenerate interval `b < a` is handled separately in both directions: Stacks 08G1
is stated for `a ≤ b`, and for `b < a` the object is zero, which the Tor-amplitude conditions
then give directly.

## References

* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 0654](https://stacks.math.columbia.edu/tag/0654)
* [Stacks Project, Tag 0653](https://stacks.math.columbia.edu/tag/0653)
* [Stacks Project, Tag 05VB](https://stacks.math.columbia.edu/tag/05VB)
* [Stacks Project, Tag 05VC](https://stacks.math.columbia.edu/tag/05VC)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject

universe u v w d

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

namespace Stacks.SheafOfModules.DerivedTensorProduct

/-! ### Preliminaries -/

/-- A zero module is flat: it is free on the empty basis. -/
private theorem flat_of_isZero {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (hM : IsZero M) :
    Module.Flat R M :=
  have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp hM
  Module.Flat.of_free

/-- Canonical Tor amplitude in `[a, b]` bounds the cohomology of the object itself to `[a, b]`:
a flat representative concentrated in `[a, b]`, which Stacks 0654 produces, has no cohomology
outside `[a, b]`. -/
private theorem isZero_homology_of_hasTorAmplitudeCanonical {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (a b i : ℤ)
    (hK : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R K a b)
    (hi : i ∉ Set.Icc a b) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) := by
  obtain ⟨L, -, hGE, hLE, ⟨e⟩⟩ :=
    (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative R K a b).1 hK
  have hLi : IsZero (L.X i) := by
    rcases (by simpa only [Set.mem_Icc, not_and_or, not_le] using hi : i < a ∨ b < i) with
      hlt | hgt
    · exact L.isZero_of_isStrictlyGE a i hlt
    · exact L.isZero_of_isStrictlyLE b i hgt
  exact (ShortComplex.isZero_homology_of_isZero_X₂ (L.sc i) hLi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app L)

/-- A site with a conservative family of points has one indexed by *all* of its points: a family
containing a conservative one is conservative. This is the shape in which the stalkwise criteria
of Stacks 05VC and of the module-valued form of Stacks 05V3 take the family. -/
private theorem isConservativeFamilyOfPoints_id {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (hJ : J.HasConservativeFamily.{w}) :
    (ObjectProperty.ofObj (id : J.Point.{w} → J.Point.{w})).IsConservativeFamilyOfPoints := by
  obtain ⟨S, hS⟩ := hJ
  refine (GrothendieckTopology.isConservativeFamily_iff_ofObj _).1 (fun φ hφ => hS φ ?_)
  exact fun q => hφ q.1

/-! ### Stacks 0DJJ -/

variable {Y : RingedSite.{u, v, w}} [LocallySmall.{w} Y.C]
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [hd : HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} Y)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Y.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **Stacks 0DJJ (1).** If an object `E` of `D(O)` has Tor amplitude in `[a, b]`, then for every
point `Φ` of the site its derived stalk `E_Φ` has Tor amplitude in `[a, b]` as an object of
`D(O_Φ)`.

By Stacks 08G1, `E` is represented by a complex `K` of flat `O`-modules vanishing outside
`[a, b]`. The stalk functor is exact, so `K_Φ` represents `E_Φ`; its terms are flat by Stacks
05VB and vanish outside `[a, b]`; so Stacks 0654 applies.

Tor amplitude is measured here against an arbitrary derived tensor product datum `T` on the
site, which is what makes the sections universe `w` free of the site's hom universe `v`. The
form of Stacks 0DJJ (1) at *the* derived tensor product of the site, the one of Stacks 06YU, is
`hasTorAmplitudeCanonical_derivedModuleFiber_canonical` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.StalksCanonical`. -/
@[sga "6 I 5.6.2" "special case"]
theorem hasTorAmplitudeCanonical_derivedModuleFiber (T : DerivedTensorProduct.{u, v, w, d} Y)
    (E : RingedSite.DerivedModules.{u, v, w, d} Y) (a b : ℤ)
    (hamp : HasTorAmplitude T E a b) (Φ : Y.J.Point.{w}) :
    letI : HasDerivedCategory.{d}
        (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Y.O)) := hd
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
      ((Φ.presheafFiber (A := CommRingCat.{w})).obj Y.O.obj)
      ((Stacks.derivedModuleFiber Φ Y.O).obj E) a b := by
  let : HasDerivedCategory.{d}
      (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Y.O)) := hd
  set R := (Φ.presheafFiber (A := CommRingCat.{w})).obj Y.O.obj with hR
  set F := Stacks.sheafModuleFiberOfCommRing Φ Y.O with hF
  by_cases hab : a ≤ b
  · obtain ⟨K, hflat, hzero, ⟨e⟩⟩ :=
      exists_flatRepresentative_of_hasTorAmplitude T E a b hab hamp
    refine (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative
      R _ a b).2 ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K, ?_, ?_, ?_, ⟨?_⟩⟩
    · exact fun i => Stacks.isFlatModuleStalk_of_isFlat_freeUniverse Y.O (K.X i) Φ (hflat i)
    · rw [CochainComplex.isStrictlyGE_iff]
      exact fun i hi => F.map_isZero (hzero i (by simp only [Set.mem_Icc]; omega))
    · rw [CochainComplex.isStrictlyLE_iff]
      exact fun i hi => F.map_isZero (hzero i (by simp only [Set.mem_Icc]; omega))
    · exact F.mapDerivedCategory.mapIso e.symm ≪≫ F.mapDerivedCategoryFactors.app K
  · have h₁ : E.IsGE a := isGE_of_hasTorAmplitude T E hamp
    have h₂ : E.IsLE b := isLE_of_hasTorAmplitude T E hamp
    have hEzero : IsZero E := DerivedCategory.TStructure.t.isZero E b a (by omega)
    have hFzero : IsZero ((Stacks.derivedModuleFiber Φ Y.O).obj E) := Functor.map_isZero _ hEzero
    refine (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative
      R _ a b).2 ⟨0, fun i => flat_of_isZero _ ?_, ?_, ?_, ⟨?_⟩⟩
    · exact (HomologicalComplex.eval (ModuleCat.{w} R) (ComplexShape.up ℤ) i).map_isZero
        (isZero_zero _)
    · rw [CochainComplex.isStrictlyGE_iff]
      exact fun i _ => (HomologicalComplex.eval (ModuleCat.{w} R)
        (ComplexShape.up ℤ) i).map_isZero (isZero_zero _)
    · rw [CochainComplex.isStrictlyLE_iff]
      exact fun i _ => (HomologicalComplex.eval (ModuleCat.{w} R)
        (ComplexShape.up ℤ) i).map_isZero (isZero_zero _)
    · exact hFzero.iso (DerivedCategory.Q.map_isZero (isZero_zero _))

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Y.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- The derived stalk of `E` at a point `Φ` having Tor amplitude in `[a, b]`, the stalk of the
cohomology of `E` vanishes outside `[a, b]`: the stalk functor is exact. -/
private theorem isZero_sheafModuleFiber_homology_of_hasTorAmplitudeCanonical
    (E : RingedSite.DerivedModules.{u, v, w, d} Y) (a b : ℤ) (Φ : Y.J.Point.{w})
    (hE :
      letI : HasDerivedCategory.{d}
          (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Y.O)) := hd
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        ((Φ.presheafFiber (A := CommRingCat.{w})).obj Y.O.obj)
        ((Stacks.derivedModuleFiber Φ Y.O).obj E) a b)
    (i : ℤ) (hi : i ∉ Set.Icc a b) :
    IsZero ((Stacks.sheafModuleFiber Φ (Stacks.commRingSheafToRingSheaf.{v, u, w} Y.O)).obj
      ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} Y) i).obj E)) := by
  let : HasDerivedCategory.{d}
      (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Y.O)) := hd
  have hstalk : IsZero ((Stacks.sheafModuleFiberOfCommRing Φ Y.O).obj
      ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} Y) i).obj E)) :=
    (isZero_homology_of_hasTorAmplitudeCanonical _ a b i hE hi).of_iso
      (((Stacks.sheafModuleFiberOfCommRing Φ Y.O).mapDerivedCategoryHomologyIso i).app E).symm
  rw [ModuleCat.isZero_iff_subsingleton] at hstalk ⊢
  exact hstalk

/-- The core of Stacks 0DJJ (2): `E` has Tor amplitude in `[a, b]` as soon as its derived
stalk at every member of one conservative family of points does. -/
private theorem hasTorAmplitude_of_forall_derivedModuleFiber_core
    (T : DerivedTensorProduct.{u, v, w, d} Y)
    (E : RingedSite.DerivedModules.{u, v, w, d} Y) (a b : ℤ)
    {t : Type*} (p : t → Y.J.Point.{w})
    (hp : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    (hE : ∀ k : t,
      letI : HasDerivedCategory.{d}
          (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Y.O)) := hd
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (((p k).presheafFiber (A := CommRingCat.{w})).obj Y.O.obj)
        ((Stacks.derivedModuleFiber (p k) Y.O).obj E) a b)
    (hhom : ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} Y) i).obj E)) :
    HasTorAmplitude T E a b := by
  classical
  let : HasDerivedCategory.{d}
      (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Y.O)) := hd
  have hEGE : E.IsGE a := (DerivedCategory.isGE_iff E a).2
    (fun i hi => hhom i (by simp only [Set.mem_Icc]; omega))
  have hELE : E.IsLE b := (DerivedCategory.isLE_iff E b).2
    (fun i hi => hhom i (by simp only [Set.mem_Icc]; omega))
  by_cases hab : a ≤ b
  · obtain ⟨M, hMLE, ⟨eM⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE E b
    let Pflat : ObjectProperty (RingedSite.Modules.{u, v, w} Y) := fun G =>
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O) G
    let _ : Pflat.ContainsZero :=
      ⟨⟨kernel (𝟙 (_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))), isZero_kernel_of_mono _,
          isFlat_kernel_id_unit⟩⟩
    have hcover : ∀ G : RingedSite.Modules.{u, v, w} Y,
        ∃ (G' : RingedSite.Modules.{u, v, w} Y) (_ : Pflat G') (f : G' ⟶ G), Epi f := by
      intro G
      obtain ⟨G', f, hG', hf⟩ := Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat Y.O G
      exact ⟨G', hG', f, hf⟩
    obtain ⟨P, f, -, hf, hPflat, hPLE⟩ :=
      (CochainComplex.exists_quasiIso_prop Pflat hcover b).1 M
    let _ : QuasiIso f := hf
    have eP : DerivedCategory.Q.obj P ≅ E := asIso (DerivedCategory.Q.map f) ≪≫ eM.symm
    have hPGE : P.IsGE a :=
      (DerivedCategory.isGE_Q_obj_iff P a).1 (DerivedCategory.TStructure.t.isGE_of_iso eP.symm a)
    let _ : P.IsGE a := hPGE
    have hCoker : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O)
        (cokernel (P.d (a - 1) a)) := by
      refine Stacks.isFlat_of_forall_isFlatModuleStalk Y.O _ p hp (fun k => ?_)
      set R := ((p k).presheafFiber (A := CommRingCat.{w})).obj Y.O.obj with hR
      set F := Stacks.sheafModuleFiberOfCommRing (p k) Y.O with hF
      set Pp := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P with hPp
      have hiso : (Stacks.derivedModuleFiber (p k) Y.O).obj E ≅ DerivedCategory.Q.obj Pp :=
        F.mapDerivedCategory.mapIso eP.symm ≪≫ F.mapDerivedCategoryFactors.app P
      have hrep : StacksDraft.TorAmplitude.HasFlatRepresentative
          (DerivedCategory.Q.obj Pp) a b :=
        StacksDraft.TorAmplitude.hasFlatRepresentative_of_iso hiso
          ((StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative
            R _ a b).1 (hE k))
      have hgen : StacksDraft.TorAmplitude.HasTorAmplitude
          (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
          (StacksDraft.TorAmplitude.canonicalTensorComparison R)
          (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)
          (DerivedCategory.Q.obj Pp) a b :=
        (StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative
          (StacksDraft.TorAmplitude.canonicalTensorComparison R)
          (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) _ a b).2 hrep
      have hbdd : StacksDraft.TorAmplitude.BoundedAbove Pp :=
        ⟨b, fun n hn => F.map_isZero (P.isZero_of_isStrictlyLE b n hn)⟩
      have hcok : Module.Flat R
          (cokernel (F.map (P.d (a - 1) a)) : ModuleCat.{w} R) :=
        StacksDraft.TorAmplitude.cokernel_flat_of_torAmplitude Pp a b hbdd
          (fun n => Stacks.isFlatModuleStalk_of_isFlat_freeUniverse Y.O (P.X n) (p k)
            (hPflat n)) hgen
      exact Module.Flat.of_linearEquiv (PreservesCokernel.iso F (P.d (a - 1) a)).toLinearEquiv
    have eOpCoker : P.opcycles a ≅
        (cokernel (P.d (a - 1) a) : RingedSite.Modules.{u, v, w} Y) :=
      IsColimit.coconePointUniqueUpToIso
        (P.opcyclesIsCokernel (a - 1) a (by simp)) (colimit.isColimit _)
    have hTruncFlat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w}
        (O := Y.O) ((P.truncGE a).X i) := by
      intro i
      rcases lt_trichotomy i a with hlt | heq | hgt
      · exact isFlat_of_isZero _ ((P.truncGE a).isZero_of_isStrictlyGE a i hlt)
      · rw [heq]
        exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso Y.O
          (eOpCoker.symm ≪≫ (P.truncGEXIsoOpcycles a).symm) hCoker
      · exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso Y.O
          (P.truncGEXIso a i hgt).symm (hPflat i)
    refine hasTorAmplitude_of_flatRepresentative T E a b (P.truncGE a) hTruncFlat ?_
      ((asIso (DerivedCategory.Q.map (P.πTruncGE a))).symm ≪≫ eP)
    intro i hi
    rcases (by simpa only [Set.mem_Icc, not_and_or, not_le] using hi : i < a ∨ b < i) with
      hlt | hgt
    · exact (P.truncGE a).isZero_of_isStrictlyGE a i hlt
    · exact (P.isZero_of_isStrictlyLE b i hgt).of_iso (P.truncGEXIso a i (by omega))
  · have hEzero : IsZero E := DerivedCategory.TStructure.t.isZero E b a (by omega)
    intro G i _
    exact Functor.map_isZero (DerivedCategory.homologyFunctor
      (RingedSite.Modules.{u, v, w} Y) i)
      (Functor.map_isZero (T.tensor.flip.obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} Y) 0).obj G)) hEzero)

/-- **Stacks 0DJJ (2).** On a ringed site whose underlying site has a conservative family of
points, an object `E` of `D(O)` has Tor amplitude in `[a, b]` as soon as its derived stalk at
every point does.

The cohomology of `E` is bounded to `[a, b]` by the stalks, so `E` is represented by a complex
of flat `O`-modules vanishing above `b` — flat modules cover, by Stacks 03EW — and the truncation
of that complex at `a` is the representative Stacks 08G1 asks for: its only new term is
`Coker(d^{a-1})`, whose stalks are the cokernels of the differentials of the stalk complexes and
are therefore flat by Stacks 0653, so that it is flat by Stacks 05VC.

As for part (1), Tor amplitude is measured against an arbitrary derived tensor product datum
`T`; the form of Stacks 0DJJ (2) at the derived tensor product of Stacks 06YU is
`hasTorAmplitude_canonical_of_forall_derivedModuleFiber` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.StalksCanonical`. -/
@[sga "6 I 5.6.2" "partial", sga "6 III 3.3" "(ii) ⇒ (i)"]
theorem hasTorAmplitude_of_forall_derivedModuleFiber
    (T : DerivedTensorProduct.{u, v, w, d} Y)
    (E : RingedSite.DerivedModules.{u, v, w, d} Y) (a b : ℤ)
    (hY : Y.J.HasConservativeFamily.{w})
    (hE : ∀ Φ : Y.J.Point.{w},
      letI : HasDerivedCategory.{d}
          (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Y.O)) := hd
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        ((Φ.presheafFiber (A := CommRingCat.{w})).obj Y.O.obj)
        ((Stacks.derivedModuleFiber Φ Y.O).obj E) a b) :
    HasTorAmplitude T E a b :=
  hasTorAmplitude_of_forall_derivedModuleFiber_core T E a b id
    (isConservativeFamilyOfPoints_id Y.J hY) hE fun i hi =>
      Stacks.isZero_of_forall_isZero_sheafModuleFiber _ (isConservativeFamilyOfPoints_id Y.J hY)
        fun Ψ => isZero_sheafModuleFiber_homology_of_hasTorAmplitudeCanonical E a b Ψ.obj
          (hE Ψ.obj) i hi

/-! ### Stacks 0DJJ (2) at a chosen conservative family -/

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Y.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- The cohomology of `E` vanishes outside `[a, b]` as soon as the derived stalk of `E` at every
member of one conservative family of points has Tor amplitude in `[a, b]`. -/
private theorem isZero_homology_of_forall_hasTorAmplitudeCanonical_family
    (E : RingedSite.DerivedModules.{u, v, w, d} Y) (a b : ℤ)
    {t : Type*} (p : t → Y.J.Point.{w})
    (hp : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    (hE : ∀ k : t,
      letI : HasDerivedCategory.{d}
          (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Y.O)) := hd
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (((p k).presheafFiber (A := CommRingCat.{w})).obj Y.O.obj)
        ((Stacks.derivedModuleFiber (p k) Y.O).obj E) a b)
    (i : ℤ) (hi : i ∉ Set.Icc a b) :
    IsZero ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} Y) i).obj E) := by
  refine Stacks.isZero_of_forall_isZero_sheafModuleFiber _ hp (fun Ψ => ?_)
  obtain ⟨k, hk⟩ := (ObjectProperty.ofObj_iff p Ψ.obj).1 Ψ.property
  exact isZero_sheafModuleFiber_homology_of_hasTorAmplitudeCanonical E a b Ψ.obj (hk ▸ hE k) i hi

/-- **Stacks 0DJJ (2) tested on one conservative family of points.** An object `E` of `D(O)` has
Tor amplitude in `[a, b]` as soon as its derived stalk at every member of a single conservative
family of points of the site does.

This is the form of Stacks 0DJJ (2) that a site with a *named* conservative family — the site of
opens of a topological space and its topological points, say — can use: the hypothesis is only
asked for at the points of the given family, not at every point of the site. The proof is the
source's: the cohomology of `E` is bounded to `[a, b]` by those stalks, so `E` is represented by a
complex of flat `O`-modules vanishing above `b` — flat modules cover, by Stacks 03EW — and the
truncation of that complex at `a` is the representative Stacks 08G1 asks for, its one new term
`Coker(d^{a-1})` being flat because its stalks along the family are, by Stacks 0653 and Stacks
05VC. -/
@[sga "4 XVII 4.2.8" "Clause (iii)", sga "6 I 5.6.2" "partial"]
theorem hasTorAmplitude_of_forall_derivedModuleFiber_family
    (T : DerivedTensorProduct.{u, v, w, d} Y)
    (E : RingedSite.DerivedModules.{u, v, w, d} Y) (a b : ℤ)
    {t : Type*} (p : t → Y.J.Point.{w})
    (hp : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    (hE : ∀ k : t,
      letI : HasDerivedCategory.{d}
          (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Y.O)) := hd
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (((p k).presheafFiber (A := CommRingCat.{w})).obj Y.O.obj)
        ((Stacks.derivedModuleFiber (p k) Y.O).obj E) a b) :
    HasTorAmplitude T E a b :=
  hasTorAmplitude_of_forall_derivedModuleFiber_core T E a b p hp hE
    (isZero_homology_of_forall_hasTorAmplitudeCanonical_family E a b p hp hE)

end Stacks.SheafOfModules.DerivedTensorProduct

end
