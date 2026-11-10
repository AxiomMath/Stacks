module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmoothInputs.FibreDimensionFormula
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.FibreRegularSequence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.KrullDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.OpenImmersionRegular
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.CompositeFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Locus
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion

/-!
# Quasi-finite slices through Cohen–Macaulay points

Let `f : X ⟶ S` be locally of finite presentation and let `x : X` be a point that is closed in
its fibre and at which `f` is Cohen–Macaulay.  Then `x` lies on a subscheme `Z ⊆ X` which is
regularly immersed, flat, locally of finite presentation and locally quasi-finite over `S`, and
whose fibre over `f x` is the single point `x`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeRegularSliceStatement`: the statement of Stacks tag 06LI, as
  a proposition.

## Main results

* `Stacks.AlgebraicGeometry.exists_regularImmersion_flat_locallyQuasiFinite_singleton_fiber`:
  the slice, conditional on `Stacks.AlgebraicGeometry.RelativeRegularSliceStatement`.

## References

* [Stacks Project, Lemma 37.22.3 (Tag 0570)](https://stacks.math.columbia.edu/tag/0570)
* [EGA IV, Proposition 17.16.1]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

/-- The isomorphism of stalks induced by an equality of points acts on germs as the dependent
rewrite along that equality. -/
private theorem stalkCongr_hom_eq_cast {T : TopCat.{u}} (F : T.Presheaf CommRingCat)
    {x y : T} (e : x = y) (a : F.stalk x) :
    (F.stalkCongr (.of_eq e)).hom.hom a = e ▸ a := by
  cases e
  simp [TopCat.Presheaf.stalkCongr]

/-- The inverse of the isomorphism of stalks induced by an equality of points acts on germs as
the dependent rewrite along the reversed equality. -/
private theorem stalkCongr_inv_eq_cast {T : TopCat.{u}} (F : T.Presheaf CommRingCat)
    {x y : T} (e : x = y) (a : F.stalk y) :
    (F.stalkCongr (.of_eq e)).inv.hom a = e.symm ▸ a := by
  cases e
  simp [TopCat.Presheaf.stalkCongr]

/-- If a point is isolated in its fibre, then it is the only point of some open neighbourhood
mapping to its image. -/
private theorem exists_open_nhds_unique_in_fibre {U X : Scheme.{u}} (g : U ⟶ X) (u : U)
    (hiso : IsOpen ({g.asFiber u} : Set (g.fiber (g u)))) :
    ∃ W : U.Opens, u ∈ W.1 ∧ ∀ z ∈ W.1, g z = g u → z = u := by
  let e := g.fiberHomeo (g u)
  let F : Set U := g ⁻¹' {g u}
  have hsub : IsOpen (Set.singleton (⟨u, rfl⟩ : F)) := by
    have himage : e '' ({g.asFiber u} : Set (g.fiber (g u))) =
        Set.singleton (⟨u, rfl⟩ : F) := by
      rw [Set.image_singleton]
      congr 1
      apply Subtype.ext
      simp [e]
    rw [← himage]
    exact e.isOpen_image.mpr hiso
  obtain ⟨W, hW, hWpre⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hsub
  refine ⟨⟨W, hW⟩, ?_, ?_⟩
  · have hmem : (⟨u, rfl⟩ : F) ∈ Subtype.val ⁻¹' W := by
      rw [hWpre]
      exact Set.mem_singleton_iff.mpr rfl
    change u ∈ W
    simpa using hmem
  · intro z hz hzg
    have hz' : (⟨z, hzg⟩ : F) ∈ Subtype.val ⁻¹' W := hz
    rw [hWpre] at hz'
    exact congrArg Subtype.val (Set.mem_singleton_iff.mp hz')

/-- Restricting a regular immersion which is flat, of finite presentation and quasi-finite at a
point to a suitable open neighbourhood of that point makes it locally quasi-finite with the
point alone in its fibre. -/
private theorem exists_open_restriction_singleton_fiber {X S Z : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) (z : Z) (hi : IsImmersion i) (hregular : IsRegularImmersion i)
    (hflat : Flat (i ≫ f)) (hlfp : LocallyOfFinitePresentation (i ≫ f))
    (hqf : quasiFiniteAt (i ≫ f) z) :
    ∃ (W : Z.Opens) (hz : z ∈ W.1),
      let j : W.toScheme ⟶ X := W.ι ≫ i
      letI : IsImmersion j := by infer_instance
      IsRegularImmersion j ∧ Flat (j ≫ f) ∧
        LocallyOfFinitePresentation (j ≫ f) ∧ LocallyQuasiFinite (j ≫ f) ∧
        {w : W.toScheme | (j ≫ f) w = f (i z)} = {⟨z, hz⟩} := by
  classical
  let g := i ≫ f
  let : LocallyOfFinitePresentation g := hlfp
  let : LocallyOfFiniteType g := inferInstance
  let Wqf := quasiFiniteLocus g
  have hzqf : z ∈ Wqf.1 := (mem_quasiFiniteLocus_iff g z).2 hqf
  have hqfpoint : g.QuasiFiniteAt z := by simpa [g] using hqf.2
  have hiso : IsOpen ({g.asFiber z} : Set (g.fiber (g z))) :=
    Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hqfpoint
  obtain ⟨Wiso, hziso, hsingle⟩ := exists_open_nhds_unique_in_fibre g z hiso
  let W : Z.Opens := Wqf ⊓ Wiso
  have hz : z ∈ W.1 := ⟨hzqf, hziso⟩
  have hWqf : W.1 ≤ Wqf.1 := inf_le_left
  have hWiso : W.1 ≤ Wiso.1 := inf_le_right
  let : IsImmersion i := hi
  let j : W.toScheme ⟶ X := W.ι ≫ i
  have hj : IsImmersion j := inferInstance
  have hregular' : IsRegularImmersion j :=
    isRegularImmersion_comp W.ι i (isRegularImmersion_ι W) hregular
  let r := Scheme.Hom.resLE (𝟙 Z) Wqf W hWqf
  have hr : r ≫ Wqf.ι = W.ι := by
    simpa [r] using (Scheme.Hom.resLE_comp_ι (f := 𝟙 Z) (U := Wqf) (V := W) hWqf)
  have : IsOpenImmersion (r ≫ Wqf.ι) := by rw [hr]; infer_instance
  have : IsOpenImmersion r := IsOpenImmersion.of_comp r Wqf.ι
  have hfactor : W.ι ≫ g = r ≫ (Wqf.ι ≫ g) := by rw [← hr, Category.assoc]
  have hfqf : Flat (j ≫ f) ∧ LocallyOfFinitePresentation (j ≫ f) ∧
      LocallyQuasiFinite (j ≫ f) := by
    have : LocallyQuasiFinite (Wqf.ι ≫ g) := locallyQuasiFinite_quasiFiniteLocus g
    rw [show j ≫ f = r ≫ (Wqf.ι ≫ g) from hfactor]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hfiber : {w : W.toScheme | (j ≫ f) w = f (i z)} = {⟨z, hz⟩} := by
    ext w
    constructor
    · intro hw
      refine Subtype.ext (hsingle (W.ι w) (hWiso w.property) ?_)
      simpa [g, j] using hw
    · rintro rfl
      rfl
  exact ⟨W, hz, hregular', hfqf.1, hfqf.2.1, hfqf.2.2, hfiber⟩

/-- **The statement of Stacks tag 06LI**: fibre-regular local equations lift to a relative regular
immersion on an affine neighbourhood, preserved by every base change. -/
abbrev RelativeRegularSliceStatement : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X) {r : ℕ} (h : Fin r → X.presheaf.stalk x)
    [LocallyOfFinitePresentation f], IsFlatAt f.toLRSHom.toShHom x →
    RingTheory.Sequence.IsRegular ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
      (List.ofFn fun i : Fin r =>
        ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom ((f.fiberι_asFiber x).symm ▸ h i)) →
    ∃ (U : X.affineOpens) (hx : x ∈ U.1) (a : Fin r → Γ(U.1.toScheme, ⊤)),
      let y : U.1.toScheme := ⟨x, hx⟩
      let I : U.1.toScheme.IdealSheafData :=
        Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn a))
      (∀ i : Fin r, (U.1.ι.stalkMap y).hom ((show U.1.ι y = x by rfl).symm ▸ h i) =
          U.1.toScheme.presheaf.germ ⊤ y (by trivial) (a i)) ∧
      y ∈ I.support ∧
      IsRegularImmersion I.subschemeι ∧
      Flat (I.subschemeι ≫ U.1.ι ≫ f) ∧
      LocallyOfFinitePresentation (I.subschemeι ≫ U.1.ι ≫ f) ∧
      ∀ (S' : Scheme.{u}) (g : S' ⟶ S),
        IsRegularImmersion (pullback.snd I.subschemeι (pullback.fst (U.1.ι ≫ f) g))

/-- **Stacks Project, Tag 0570, conditional on Tag 06LI.**  A Cohen–Macaulay point closed in its
fibre lies on a regular immersed, flat, locally finitely presented, locally quasi-finite slice
with singleton fibre at that point. -/
theorem exists_regularImmersion_flat_locallyQuasiFinite_singleton_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X)
    (hCM : ∃ hf : ∀ y : S, IsLocallyNoetherian (f.fiber y),
      Scheme.Hom.IsCohenMacaulayAt f hf x)
    (hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x))))
    (hslice : RelativeRegularSliceStatement.{u}) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (z : Z) (hi : IsImmersion i),
      letI := hi
      i z = x ∧ IsRegularImmersion i ∧
        Flat (i ≫ f) ∧ LocallyOfFinitePresentation (i ≫ f) ∧
        LocallyQuasiFinite (i ≫ f) ∧
        {z' : Z | (i ≫ f) z' = f x} = {z} := by
  classical
  obtain ⟨hf, hCM⟩ := hCM
  have := hf (f x)
  obtain ⟨r, h, hdim, hreg⟩ :=
    exists_lift_fibre_isRegular_of_isCohenMacaulayLocalRing f x hf hCM.2
  obtain ⟨U, hxU, a, hdata⟩ := hslice f x h hCM.1 hreg
  let y : U.1.toScheme := ⟨x, hxU⟩
  let I : U.1.toScheme.IdealSheafData :=
    Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn a))
  obtain ⟨z, hz⟩ : y ∈ Set.range I.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hdata.2.1
  let i : I.subscheme ⟶ X := I.subschemeι ≫ U.1.ι
  have hi : IsImmersion i := inferInstance
  have hix : i z = x := by
    change U.1.ι (I.subschemeι z) = x
    rw [hz]
    rfl
  have hregular : IsRegularImmersion i :=
    isRegularImmersion_comp I.subschemeι U.1.ι hdata.2.2.1 (isRegularImmersion_ι U.1)
  rcases hdata with ⟨hsections, -, -, hflatData, hlfpData, -⟩
  subst hix
  let g := i ≫ f
  let : LocallyOfFinitePresentation g := hlfpData
  let : LocallyOfFiniteType g := inferInstance
  have hbase : g z = f (i z) := by simp [g]
  have hbaseComp : (i ≫ f) z = f (i z) := by simp
  let w : (i ≫ f).fiber (f (i z)) := hbaseComp ▸ (i ≫ f).asFiber z
  let j : (i ≫ f).fiber (f (i z)) ⟶ f.fiber (f (i z)) :=
    AlgebraicGeometry.fiberMapOfSourceHom i f (f (i z))
  have hpb := (AlgebraicGeometry.fiberMapOfSourceHom_isPullback i f (f (i z))).flip
  have hj : IsImmersion j := MorphismProperty.of_isPullback hpb hi
  have hw : (i ≫ f).fiberι (f (i z)) w = z := by
    dsimp [w]
    cases hbase
    change (i ≫ f).fiberι (f (i z)) ((i ≫ f).asFiber z) = z
    exact Scheme.Hom.fiberι_asFiber (i ≫ f) z
  have hsource : f.fiberι (f (i z)) (j w) = i z := by
    simpa only [Scheme.Hom.comp_apply, hw] using (congrArg (fun k => k w) hpb.w).symm
  have hjpoint : j w = f.asFiber (i z) := by
    refine (f.fiberι (f (i z))).isEmbedding.injective ?_
    simpa only [Scheme.Hom.fiberι_asFiber] using hsource
  have hpre : j ⁻¹' {f.asFiber (i z)} = {w} := by
    ext w'
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hw' => j.isEmbedding.injective (hw'.trans hjpoint.symm),
      by rintro rfl; exact hjpoint⟩
  have hclosedg : IsClosed ({g.asFiber z} : Set (g.fiber (g z))) := by
    have hc' : IsClosed ({w} : Set (g.fiber (f (i z)))) := by
      simpa [hpre] using hclosed.preimage j.continuous
    cases hbase
    exact hc'
  let : Algebra (S.residueField (g z)) (I.subscheme.residueField z) :=
    (g.residueFieldMap z).hom.toAlgebra
  have hfinite := (isClosed_asFiber_iff_finite_residueField g z).mp hclosedg
  let : Module.Finite (S.residueField (g z)) (I.subscheme.residueField z) := hfinite
  have htrdeg : Algebra.trdeg (S.residueField (g z)) (I.subscheme.residueField z) = 0 :=
    trdeg_eq_zero
  let R : Type u := (f.fiber (f (i z))).presheaf.stalk (f.asFiber (i z))
  let Q : Type u := ((i ≫ f).fiber (f (i z))).presheaf.stalk w
  let ss := List.ofFn fun k : Fin r =>
    ((f.fiberι (f (i z))).stalkMap (f.asFiber (i z))).hom
      ((f.fiberι_asFiber (i z)).symm ▸ h k)
  have hreg' : RingTheory.Sequence.IsRegular R ss := by simpa [R, ss] using hreg
  let e := (f.fiber (f (i z))).presheaf.stalkCongr (.of_eq hjpoint.symm)
  let φ : R →+* Q := (e.hom ≫ j.stalkMap w).hom
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨q', hq'⟩ := j.stalkMap_surjective w q
    refine ⟨e.inv.hom q', ?_⟩
    change (j.stalkMap w).hom (e.hom.hom (e.inv.hom q')) = q
    rw [e.inv_hom_id_apply, hq']
  have hzeroi (k : Fin r) : (i.stalkMap z).hom (h k) = 0 := by
    rw [Scheme.Hom.stalkMap_comp]
    change (I.subschemeι.stalkMap z).hom
      ((U.1.ι.stalkMap (I.subschemeι z)).hom
        ((show U.1.ι (I.subschemeι z) = i z by dsimp [i]).symm ▸ h k)) = 0
    have hsectionAt : (U.1.ι.stalkMap (I.subschemeι z)).hom
        ((show U.1.ι (I.subschemeι z) = i z by dsimp [i]).symm ▸ h k) =
          U.1.toScheme.presheaf.germ ⊤ (I.subschemeι z) (by simp) (a k) := by
      convert hsections k using 1
      · exact congrArg (fun p => ↥(U.1.toScheme.presheaf.stalk p)) hz
      all_goals
        cases hz
        exact HEq.rfl
    rw [hsectionAt]
    let Utop : U.1.toScheme.affineOpens := ⟨⊤, isAffineOpen_top _⟩
    let ρ : Γ(U.1.toScheme, ⊤) →+* Γ(U.1.toScheme, Utop.1) :=
      (U.1.toScheme.presheaf.map (homOfLE le_top).op).hom
    have hmap : ρ (a k) ∈ Ideal.map ρ (Ideal.ofList (List.ofFn a)) :=
      Ideal.mem_map_of_mem ρ (Ideal.subset_span (List.mem_ofFn.mpr ⟨k, rfl⟩))
    have hρ : ρ = RingHom.id _ := by
      ext t
      dsimp [ρ, Utop]
      change (X.presheaf.map ((Scheme.Hom.opensFunctor U.1.ι).map (𝟙 ⊤)).op).hom t = t
      have hopen : (Scheme.Hom.opensFunctor U.1.ι).map (𝟙 ⊤) = 𝟙 _ := Subsingleton.elim _ _
      rw [hopen]
      simp
      rfl
    have hmem : a k ∈ I.ideal Utop := by
      change a k ∈
        (Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn a))).ideal Utop
      rw [Scheme.IdealSheafData.ofIdealTop_ideal]
      change a k ∈ Ideal.map ρ (Ideal.ofList (List.ofFn a))
      have hρk : ρ (a k) = a k := by rw [hρ]; rfl
      rwa [← hρk]
    have happzero : (I.subschemeι.app Utop).hom (a k) = 0 := by
      refine RingHom.mem_ker.mp ?_
      rwa [Scheme.IdealSheafData.ker_subschemeι_app I Utop]
    have happzeroTop : (I.subschemeι.app ⊤).hom (a k) = 0 := by
      simpa [Utop] using happzero
    rw [Scheme.Hom.germ_stalkMap_apply, happzeroTop, map_zero]
  have heq : f.fiberι (f (i z)) (f.asFiber (i z)) = f.fiberι (f (i z)) (j w) := by
    rw [Scheme.Hom.fiberι_asFiber, hsource]
  have hpt : f.fiberι (f (i z)) (j w) = i ((i ≫ f).fiberι (f (i z)) w) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun k => k w) hpb.w.symm
  let eX1 := X.presheaf.stalkCongr (.of_eq heq)
  let eX2 := X.presheaf.stalkCongr (.of_eq hpt)
  have hcongr : (f.fiberι (f (i z))).stalkMap (f.asFiber (i z)) ≫ e.hom =
      eX1.hom ≫ (f.fiberι (f (i z))).stalkMap (j w) := by
    simpa [e, eX1] using
      (Scheme.Hom.stalkMap_congr_point (f.fiberι (f (i z))) (f.asFiber (i z)) (j w) hjpoint.symm)
  have h2' : (f.fiberι (f (i z))).stalkMap (j w) ≫ j.stalkMap w =
      eX2.hom ≫ i.stalkMap ((i ≫ f).fiberι (f (i z)) w) ≫
        ((i ≫ f).fiberι (f (i z))).stalkMap w := by
    have h2 := Scheme.Hom.stalkMap_congr_hom (j ≫ f.fiberι (f (i z)))
      (((i ≫ f).fiberι (f (i z))) ≫ i) hpb.w.symm w
    have ee := Scheme.Hom.comp_apply j (f.fiberι (f (i z))) w
    cases ee.symm
    convert h2 using 1 <;> simp [Scheme.Hom.stalkMap_comp, eX2, TopCat.Presheaf.stalkCongr]
  have hcomp : (f.fiberι (f (i z))).stalkMap (f.asFiber (i z)) ≫ e.hom ≫ j.stalkMap w =
      eX1.hom ≫ eX2.hom ≫ i.stalkMap ((i ≫ f).fiberι (f (i z)) w) ≫
        ((i ≫ f).fiberι (f (i z))).stalkMap w := by
    simp only [← Category.assoc, hcongr]
    simp only [Category.assoc, h2']
  let eX := X.presheaf.stalkCongr (.of_eq (congrArg i hw))
  let eI := I.subscheme.presheaf.stalkCongr (.of_eq hw)
  have hzeroi' (k : Fin r) :
      (i.stalkMap ((i ≫ f).fiberι (f (i z)) w)).hom (eX.inv.hom (h k)) = 0 := by
    have hcongI := Scheme.Hom.stalkMap_congr_point i ((i ≫ f).fiberι (f (i z)) w) z hw
    have heval := congrArg (fun m => m.hom (eX.inv.hom (h k))) hcongI
    have hval : eI.hom.hom
        ((i.stalkMap ((i ≫ f).fiberι (f (i z)) w)).hom (eX.inv.hom (h k))) =
        (i.stalkMap z).hom (h k) := by
      have hh : eI.hom.hom
          ((i.stalkMap ((i ≫ f).fiberι (f (i z)) w)).hom (eX.inv.hom (h k))) =
          (i.stalkMap z).hom (eX.hom.hom (eX.inv.hom (h k))) := by
        simpa only [ConcreteCategory.comp_apply] using heval
      rw [hh, eX.inv_hom_id_apply (h k)]
    refine (ConcreteCategory.bijective_of_isIso eI.hom).1 ?_
    rw [hval, hzeroi k]
    simp
  have hcast (k : Fin r) :
      eX2.hom (eX1.hom ((f.fiberι_asFiber (i z)).symm ▸ h k)) = eX.inv.hom (h k) := by
    have hpath : ((f.fiberι_asFiber (i z)).symm.trans heq).trans hpt =
        (congrArg i hw).symm := Subsingleton.elim _ _
    have h1 := stalkCongr_hom_eq_cast X.presheaf heq ((f.fiberι_asFiber (i z)).symm ▸ h k)
    have h2 := stalkCongr_hom_eq_cast X.presheaf hpt
      (heq ▸ ((f.fiberι_asFiber (i z)).symm ▸ h k))
    have h3 := stalkCongr_inv_eq_cast X.presheaf (congrArg i hw) (h k)
    change eX2.hom.hom (eX1.hom.hom ((f.fiberι_asFiber (i z)).symm ▸ h k)) = eX.inv.hom (h k)
    have hc1 : heq ▸ (f.fiberι_asFiber (i z)).symm ▸ h k =
        ((f.fiberι_asFiber (i z)).symm.trans heq) ▸ h k :=
      cast_cast_eq (β := fun p : X => X.presheaf.stalk p)
        (f.fiberι_asFiber (i z)).symm heq (h k)
    have hc1' := congrArg
      (fun t : X.presheaf.stalk ((f.fiberι (f (i z))) (j w)) => hpt ▸ t) hc1
    have hc2 : hpt ▸ ((f.fiberι_asFiber (i z)).symm.trans heq ▸ h k) =
        (((f.fiberι_asFiber (i z)).symm.trans heq).trans hpt) ▸ h k :=
      cast_cast_eq (β := fun p : X => X.presheaf.stalk p)
        ((f.fiberι_asFiber (i z)).symm.trans heq) hpt (h k)
    have hc3 := congrArg (fun p => p ▸ h k) hpath
    calc
      _ = hpt ▸ ((f.fiberι_asFiber (i z)).symm.trans heq ▸ h k) := by
        rw [h1, h2]
        exact hc1'
      _ = ((f.fiberι_asFiber (i z)).symm.trans heq).trans hpt ▸ h k := hc2
      _ = (congrArg i hw).symm ▸ h k := hc3
      _ = _ := h3.symm
  have hkill : ∀ b ∈ ss, φ b = 0 := by
    intro b hb
    rcases List.mem_ofFn.mp hb with ⟨k, rfl⟩
    change ((e.hom ≫ j.stalkMap w).hom)
      (((f.fiberι (f (i z))).stalkMap (f.asFiber (i z))).hom
        ((f.fiberι_asFiber (i z)).symm ▸ h k)) = 0
    have hval := congrArg (fun m :
        X.presheaf.stalk ((f.fiberι (f (i z))) (f.asFiber (i z))) ⟶
          ((i ≫ f).fiber (f (i z))).presheaf.stalk w =>
      m.hom ((f.fiberι_asFiber (i z)).symm ▸ h k)) hcomp
    simp only [ConcreteCategory.comp_apply] at hval
    rwa [hcast k, hzeroi' k, map_zero] at hval
  have hlen' : (ss.length : WithBot ℕ∞) = ringKrullDim R := by
    have hlength : ss.length = r := by simp [ss]
    rw [hlength]
    simpa [R, hjpoint] using hdim
  have hringdim : ringKrullDim Q = 0 :=
    ringKrullDim_eq_zero_of_surjective_of_forall_eq_zero φ hφ ss hreg' hlen' hkill
  have hringdim' : ringKrullDim ((g.fiber (g z)).presheaf.stalk (g.asFiber z)) = 0 := by
    dsimp [Q] at hringdim
    cases hbase
    exact hringdim
  have : IsLocallyNoetherian (g.fiber (g z)) := by
    have : LocallyOfFiniteType (g.fiberToSpecResidueField (g z)) := by
      change LocallyOfFiniteType (pullback.snd g (S.fromSpecResidueField (g z)))
      infer_instance
    exact LocallyOfFiniteType.isLocallyNoetherian (g.fiberToSpecResidueField (g z))
  have hdimfiber : topologicalKrullDimAt (g.fiber (g z)) (g.asFiber z) = 0 := by
    rw [topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk_add_trdeg g z, hringdim', htrdeg]
    simp
  have hqf : quasiFiniteAt g z :=
    (quasiFiniteAt_iff_fiberDimensionAt_eq_zero g z).2 hdimfiber
  obtain ⟨W, hzW, hregular', hflat', hlfp', hqf', hfiber⟩ :=
    exists_open_restriction_singleton_fiber f i z hi hregular hflatData hlfpData hqf
  let j' : W.toScheme ⟶ X := W.ι ≫ i
  let z' : W.toScheme := ⟨z, hzW⟩
  refine ⟨W.toScheme, j', z', inferInstance, rfl, hregular', hflat', hlfp', hqf', ?_⟩
  simpa [j', g] using hfiber

end Stacks.AlgebraicGeometry

end
