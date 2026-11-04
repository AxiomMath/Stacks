module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Restrict
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The zero locus and the support of a section on the small étale site

Let `B` be a big étale site containing a scheme `S` and let `F` be an abelian sheaf on the
small étale site of `S` inside `B`. A section of `F` over an object `U` of that site has a
largest Zariski open subset of `U` on which it restricts to zero, and the *support* of the
section is the complement of that open. Vanishing of the pullback of the section along an
arbitrary morphism of the small étale site is detected by the set-theoretic image of that
morphism lying in the zero locus; in particular the zero locus is the union of the images of
all the arrows along which the section dies.

## Main definitions

* `AlgebraicGeometry.SmallEtale.openObject` views a Zariski open of an object of the small
  étale site as an object of that site, with `openObjectι` its inclusion and
  `openObjectHomOfLE` the inclusion of one open in another.
* `AlgebraicGeometry.SmallEtale.factorThroughOpenObject` factors an arrow of the small étale
  site whose image lies in a Zariski open through that open.
* `AlgebraicGeometry.SmallEtale.IsZeroOpen` says that a Zariski open is the image of an open
  immersion of the small étale site along which the section vanishes.
* `AlgebraicGeometry.SmallEtale.zeroOpen` is the largest Zariski open zero locus.
* `AlgebraicGeometry.SmallEtale.supportSection` is its complement, the support.

## Main results

* `AlgebraicGeometry.SmallEtale.map_eq_zero_iff_le_zeroOpen` characterizes vanishing after an
  open immersion of the small étale site by containment of its image in the zero locus.
* `AlgebraicGeometry.SmallEtale.map_eq_zero_iff_range_subset_zeroOpen` is the same
  characterization for an arbitrary arrow of the small étale site.
* `AlgebraicGeometry.SmallEtale.isClosed_supportSection` — the support is closed.
* `AlgebraicGeometry.SmallEtale.supportSection_add_subset` and
  `AlgebraicGeometry.SmallEtale.supportSection_map_subset` — the support of a sum lies in the
  union of the supports, and a morphism of sheaves does not enlarge a support.

## Implementation notes

The zero locus is defined as the supremum of the Zariski opens of `U` which are the images of
open immersions of the small étale site along which the section vanishes.

Representing a Zariski open of an object of the small étale site as an object of that site
requires the size cutoff of `B`, since an open subscheme of a scheme below the cutoff is again
below it.

## References

* [Stacks Project, Tag 04FS](https://stacks.math.columbia.edu/tag/04FS)
* [Stacks Project, Tag 04FR](https://stacks.math.columbia.edu/tag/04FR)
* [Stacks Project, Tag 04FT](https://stacks.math.columbia.edu/tag/04FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every morphism of the small étale site is étale as a morphism of schemes. -/
public theorem etale_toScheme_map {U V : SmallEtale B S hS} (f : U ⟶ V) :
    Etale ((SmallEtale.toScheme B S hS).map f) := by
  have : Etale ((SmallEtale.toScheme B S hS).map f ≫ B.inclusion.map V.obj.hom) := by
    rw [SmallEtale.toScheme_map_comp]
    exact U.property
  exact Etale.of_comp _ (B.inclusion.map V.obj.hom)

/-- A Zariski open of an object of the small étale site, viewed as an object of the small
étale site. -/
public abbrev openObject (U : SmallEtale B S hS)
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens) : SmallEtale B S hS := by
  let V : B.Scheme := ⟨(↑W : Scheme),
    lt_of_le_of_lt (Scheme.size_coe_opens_le _ W) U.obj.left.property⟩
  let i : V ⟶ U.obj.left := B.inclusion.preimage W.ι
  refine ⟨Over.mk (i ≫ U.obj.hom), ?_⟩
  change Etale (B.inclusion.map (i ≫ U.obj.hom))
  rw [Functor.map_comp, B.inclusion.map_preimage]
  infer_instance

/-- The inclusion of a Zariski open of an object of the small étale site. -/
public def openObjectι (U : SmallEtale B S hS)
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens) : openObject B S hS U W ⟶ U :=
  ⟨Over.homMk (B.inclusion.preimage W.ι)⟩

/-- The inclusion of a Zariski open is the open immersion of that open. -/
@[simp]
public theorem openObjectι_map (U : SmallEtale B S hS)
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens) :
    (SmallEtale.toScheme B S hS).map (openObjectι B S hS U W) = W.ι := by
  let V : B.Scheme := ⟨(↑W : Scheme),
    lt_of_le_of_lt (Scheme.size_coe_opens_le _ W) U.obj.left.property⟩
  let fscheme : B.inclusion.obj V ⟶ B.inclusion.obj U.obj.left := W.ι
  show B.inclusion.map (B.inclusion.preimage fscheme) = fscheme
  exact B.inclusion.map_preimage fscheme

/-- The inclusion of a Zariski open is an open immersion of schemes. -/
public instance isOpenImmersion_openObjectι (U : SmallEtale B S hS)
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens) :
    IsOpenImmersion ((SmallEtale.toScheme B S hS).map (openObjectι B S hS U W)) := by
  rw [openObjectι_map]
  infer_instance

/-- The image of the inclusion of a Zariski open is that open. -/
@[simp]
public theorem openObjectι_range (U : SmallEtale B S hS)
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens) :
    Set.range ((SmallEtale.toScheme B S hS).map (openObjectι B S hS U W)).base = W := by
  rw [openObjectι_map]
  exact Scheme.Opens.range_ι W

/-- The open image of the inclusion of a Zariski open is that open. -/
@[simp]
public theorem openObjectι_opensRange (U : SmallEtale B S hS)
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens) :
    ((SmallEtale.toScheme B S hS).map (openObjectι B S hS U W)).opensRange = W :=
  TopologicalSpace.Opens.ext (openObjectι_range B S hS U W)

/-- The inclusion of one Zariski open of an object of the small étale site in another, as a
morphism of the small étale site. -/
public def openObjectHomOfLE (U : SmallEtale B S hS)
    {W W' : ((SmallEtale.toScheme B S hS).obj U).Opens} (h : W ≤ W') :
    openObject B S hS U W ⟶ openObject B S hS U W' := by
  refine ⟨Over.homMk (B.inclusion.preimage (Scheme.homOfLE _ h)) ?_⟩
  apply B.inclusion.map_injective
  change B.inclusion.map (_ ≫ (_ ≫ _)) = B.inclusion.map (_ ≫ _)
  simp only [Functor.map_comp, Functor.map_preimage]
  rw [← Category.assoc]
  exact congrArg (fun f => f ≫ B.inclusion.map U.obj.hom) (Scheme.homOfLE_ι _ h)

/-- The inclusion of one Zariski open in another is the corresponding open immersion of
schemes. -/
@[simp]
public theorem openObjectHomOfLE_map (U : SmallEtale B S hS)
    {W W' : ((SmallEtale.toScheme B S hS).obj U).Opens} (h : W ≤ W') :
    (SmallEtale.toScheme B S hS).map (openObjectHomOfLE B S hS U h) = Scheme.homOfLE _ h :=
  B.inclusion.map_preimage _

/-- Inclusions of Zariski opens compose. -/
@[simp]
public theorem openObjectHomOfLE_comp (U : SmallEtale B S hS)
    {W W' W'' : ((SmallEtale.toScheme B S hS).obj U).Opens} (h : W ≤ W') (k : W' ≤ W'') :
    openObjectHomOfLE B S hS U h ≫ openObjectHomOfLE B S hS U k =
      openObjectHomOfLE B S hS U (h.trans k) := by
  apply (SmallEtale.inclusion B S hS).map_injective
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  show (SmallEtale.toScheme B S hS).map (openObjectHomOfLE B S hS U h ≫
    openObjectHomOfLE B S hS U k) =
      (SmallEtale.toScheme B S hS).map (openObjectHomOfLE B S hS U (h.trans k))
  simp only [Functor.map_comp, openObjectHomOfLE_map, Scheme.homOfLE_homOfLE]

/-- The inclusion of a Zariski open in itself is the identity. -/
@[simp]
public theorem openObjectHomOfLE_refl (U : SmallEtale B S hS)
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens) :
    openObjectHomOfLE B S hS U (le_refl W) = 𝟙 _ := by
  apply (SmallEtale.inclusion B S hS).map_injective
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  show (SmallEtale.toScheme B S hS).map (openObjectHomOfLE B S hS U (le_refl W)) =
    (SmallEtale.toScheme B S hS).map (𝟙 _)
  rw [openObjectHomOfLE_map, CategoryTheory.Functor.map_id, Scheme.homOfLE_rfl]
  rfl

/-- A Zariski open on which a section restricts to zero, represented by an open immersion in
the small étale site. -/
public def IsZeroOpen (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U : SmallEtale B S hS) (s : F.obj.obj (op U))
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens) : Prop :=
  ∃ (V : SmallEtale B S hS) (f : V ⟶ U),
    IsOpenImmersion ((SmallEtale.toScheme B S hS).map f) ∧
      (W : Set ((SmallEtale.toScheme B S hS).obj U)) =
        Set.range ((SmallEtale.toScheme B S hS).map f).base ∧
      F.obj.map f.op s = 0

/-- The maximal Zariski open locus on which a section of an abelian sheaf on the small étale site
vanishes. -/
@[sga "4 VIII 6.6"]
public def zeroOpen (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U : SmallEtale B S hS) (s : F.obj.obj (op U)) :
    ((SmallEtale.toScheme B S hS).obj U).Opens :=
  sSup {W | IsZeroOpen B S hS F U s W}

/-- The support of a section of an abelian sheaf on the small étale site is the complement of its
maximal Zariski open zero locus. -/
@[stacks 04FS "support of a section", sga "4 VIII 6.6" "support of a section"]
public def supportSection (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U : SmallEtale B S hS) (s : F.obj.obj (op U)) :
    Set ((SmallEtale.toScheme B S hS).obj U) :=
  (zeroOpen B S hS F U s : Set ((SmallEtale.toScheme B S hS).obj U))ᶜ

private theorem restrict_zero_of_image_subset
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U : SmallEtale B S hS) (s : F.obj.obj (op U))
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens)
    (hW : IsZeroOpen B S hS F U s W)
    (V : SmallEtale B S hS) (k : V ⟶ U)
    (hk : Set.range ((SmallEtale.toScheme B S hS).map k).base ⊆ W) :
    F.obj.map k.op s = 0 := by
  classical
  obtain ⟨V₀, f₀, hf₀, hrange, hzero⟩ := hW
  let _ : IsOpenImmersion ((SmallEtale.toScheme B S hS).map f₀) := hf₀
  let qScheme := IsOpenImmersion.lift ((SmallEtale.toScheme B S hS).map f₀)
    ((SmallEtale.toScheme B S hS).map k) (by rw [← hrange]; exact hk)
  have hqfac : qScheme ≫ (SmallEtale.toScheme B S hS).map f₀ =
      (SmallEtale.toScheme B S hS).map k :=
    IsOpenImmersion.lift_fac _ _ _
  let qbase := B.inclusion.preimage (show
    B.inclusion.obj V.obj.left ⟶ B.inclusion.obj V₀.obj.left from qScheme)
  have hqmap : B.inclusion.map qbase = qScheme := B.inclusion.map_preimage _
  let f₀base := (Over.forget (B.obj S hS)).map
    ((SmallEtale.inclusion B S hS).map f₀)
  let kbase := (Over.forget (B.obj S hS)).map
    ((SmallEtale.inclusion B S hS).map k)
  have hmapf₀ : B.inclusion.map f₀base = (SmallEtale.toScheme B S hS).map f₀ := rfl
  have hmapk : B.inclusion.map kbase = (SmallEtale.toScheme B S hS).map k := rfl
  have hqbase : qbase ≫ f₀base = kbase := by
    apply B.inclusion.map_injective
    simpa only [Functor.map_comp, hqmap, hmapf₀, hmapk] using hqfac
  have hf₀over : f₀base ≫ U.obj.hom = V₀.obj.hom := by
    simp [f₀base]
  have kover : kbase ≫ U.obj.hom = V.obj.hom := by
    simp [kbase]
  have hqover : qbase ≫ V₀.obj.hom = V.obj.hom := by
    rw [← hf₀over, ← Category.assoc, hqbase, kover]
  let qOver : V.obj ⟶ V₀.obj := Over.homMk qbase hqover
  let q : V ⟶ V₀ := ⟨qOver⟩
  have hq : q ≫ f₀ = k := by
    apply (SmallEtale.toScheme B S hS).map_injective
    show B.inclusion.map (qbase ≫ f₀base) = B.inclusion.map kbase
    rw [hqbase]
  rw [← hq, op_comp, F.obj.map_comp]
  show (F.obj.map q.op) ((F.obj.map f₀.op) s) = 0
  rw [hzero]
  simp

/-- A section vanishing on every member of a chosen covering family vanishes: this is
separatedness of the sheaf for the sieve generated by that family. -/
public theorem section_zero_of_covering
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (V : SmallEtale B S hS) (E : PreZeroHypercover V)
    (hE : SmallEtale.IsCovering B S hS ⟨V, E⟩)
    (s : F.obj.obj (op V)) (hz : ∀ i, F.obj.map (E.f i).op s = 0) :
    s = 0 := by
  have hpre : E.presieve₀ ∈ SmallEtale.precoverage B S hS V := by
    rw [SmallEtale.mem_precoverage_iff]
    exact ⟨E, rfl, hE⟩
  have htop : Sieve.generate E.presieve₀ ∈ SmallEtale.topology B S hS V := by
    show Sieve.generate E.presieve₀ ∈
      (SmallEtale.precoverage B S hS).toGrothendieck V
    rw [Precoverage.mem_toGrothendieck_iff]
    exact Precoverage.Saturate.of V E.presieve₀ hpre
  apply F.property.isSeparated V (Sieve.generate E.presieve₀) htop s 0
  intro Y g hg
  obtain ⟨Z, k, hk, hgen, rfl⟩ := hg
  obtain ⟨i⟩ := hgen
  rw [op_comp, F.obj.map_comp, ConcreteCategory.comp_apply, hz i]
  simp

/-- Along an open immersion of the small étale site, a section restricts to zero precisely when the
image is contained in the maximal zero open. -/
@[stacks 04FS "support of a section", sga "2 XIV 1.8.2.1" "abelian, s'=0"]
public theorem map_eq_zero_iff_le_zeroOpen
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U : SmallEtale B S hS) (s : F.obj.obj (op U))
    (V : SmallEtale B S hS) (f : V ⟶ U)
    [IsOpenImmersion ((SmallEtale.toScheme B S hS).map f)] :
    F.obj.map f.op s = 0 ↔
      ((SmallEtale.toScheme B S hS).map f).opensRange ≤ zeroOpen B S hS F U s := by
  constructor
  · intro hs
    apply le_sSup
    refine ⟨V, f, inferInstance, ?_, hs⟩
    ext x
    simp [Scheme.Hom.opensRange]
  · intro h
    classical
    let E : PreZeroHypercover.{u + 1} V := {
      I₀ := ULift.{u + 1, u} {W : ((SmallEtale.toScheme B S hS).obj U).Opens |
        IsZeroOpen B S hS F U s W}
      X i := openObject B S hS V (((SmallEtale.toScheme B S hS).map f) ⁻¹ᵁ i.down.1)
      f i := openObjectι B S hS V (((SmallEtale.toScheme B S hS).map f) ⁻¹ᵁ i.down.1)
    }
    let G := SmallEtale.inclusion B S hS ⋙ Over.forget (B.obj S hS)
    let Ebase := E.map G
    have hmapEi (i : E.I₀) : (Ebase.map B.inclusion).f i =
        (SmallEtale.toScheme B S hS).map (E.f i) := by
      simp [Ebase, G, PreZeroHypercover.map, SmallEtale.toScheme,
        BigEtaleOver.toScheme]
    have hEtale : IsEtaleCovering ⟨V.obj.left, Ebase⟩ := by
      show (Ebase.map B.inclusion).presieve₀ ∈
        Scheme.etalePrecoverage (B.inclusion.obj (G.obj V))
      have hcover :
          (∀ x, ∃ i, x ∈ Set.range ((Ebase.map B.inclusion).f i)) ∧
            ∀ i, Etale ((Ebase.map B.inclusion).f i) := by
        constructor
        · intro x
          have hx0 : ((SmallEtale.toScheme B S hS).map f).base x ∈
              zeroOpen B S hS F U s := h ⟨x, rfl⟩
          obtain ⟨W, hW, hxW⟩ := TopologicalSpace.Opens.mem_sSup.mp hx0
          let i : E.I₀ := ULift.up ⟨W, hW⟩
          refine ⟨i, ?_⟩
          show ∃ y, ((Ebase.map B.inclusion).f i).base y = x
          refine ⟨⟨x, ?_⟩, ?_⟩
          · show ((SmallEtale.toScheme B S hS).map f).base x ∈ i.down.1
            exact hxW
          · rw [hmapEi i, openObjectι_map]
            rfl
        · intro i
          have hg : IsOpenImmersion ((Ebase.map B.inclusion).f i) := by
            rw [hmapEi i]
            exact isOpenImmersion_openObjectι B S hS V _
          let _ := hg
          infer_instance
      simpa only [Scheme.etalePrecoverage] using
        (Scheme.presieve₀_mem_precoverage_iff (P := @Etale)
          (Ebase.map B.inclusion)).2 hcover
    obtain ⟨R, hR, hcomb⟩ := B.exists_covering_rep ⟨V.obj.left, Ebase⟩ hEtale
    rcases R with ⟨Rtarget, Rfam⟩
    have htarget : V.obj.left = Rtarget := hcomb.1
    cases htarget
    have hRpre : (Rfam.map B.inclusion).presieve₀ ∈
        Scheme.etalePrecoverage (B.inclusion.obj V.obj.left) := hR.1
    have hRprops :
        (∀ x, ∃ i, x ∈ Set.range ((Rfam.map B.inclusion).f i)) ∧
          ∀ i, Etale ((Rfam.map B.inclusion).f i) := by
      simpa only [Scheme.etalePrecoverage] using
        (Scheme.presieve₀_mem_precoverage_iff (P := @Etale)
          (Rfam.map B.inclusion)).1 hRpre
    let Rsmall : PreZeroHypercover.{u + 1} V := {
      I₀ := Rfam.I₀
      X i := ⟨Over.mk (Rfam.f i ≫ V.obj.hom), by
        show Etale (B.inclusion.map (Rfam.f i) ≫ B.inclusion.map V.obj.hom)
        let _ : Etale (B.inclusion.map (Rfam.f i)) := hRprops.2 i
        exact Etale.etale_comp _ _⟩
      f i := ⟨Over.homMk (Rfam.f i) (by rfl)⟩
    }
    have hRsmall : SmallEtale.IsCovering B S hS ⟨V, Rsmall⟩ := by
      show B.IsCovering ⟨V.obj.left, Rsmall.map G⟩
      have hmap : Rsmall.map G = Rfam := by
        ext <;> rfl
      rw [hmap]
      exact hR
    obtain ⟨α, hX, hf⟩ := hcomb.2.symm.1
    have hzR : ∀ i, F.obj.map (Rsmall.f i).op (F.obj.map f.op s) = 0 := by
      intro i
      let j := α i
      let W := j.down.1
      have hW : IsZeroOpen B S hS F U s W := j.down.2
      have hsubset : Set.range
          ((SmallEtale.toScheme B S hS).map (Rsmall.f i ≫ f)).base ⊆ W := by
        let e := B.inclusion.map (eqToHom (hX i))
        have hArrow : B.inclusion.map (Rfam.f i) =
            e ≫ B.inclusion.map (Ebase.f j) := by
          calc
            B.inclusion.map (Rfam.f i) =
                B.inclusion.map (eqToHom (hX i) ≫ Ebase.f (α i)) :=
                  congrArg (fun q => B.inclusion.map q) (hf i)
            _ = e ≫ B.inclusion.map (Ebase.f j) := by
              simp [e, j]
        rintro x ⟨y, rfl⟩
        have hmapR : (SmallEtale.toScheme B S hS).map (Rsmall.f i) =
            B.inclusion.map (Rfam.f i) := rfl
        let z : (SmallEtale.toScheme B S hS).obj (E.X j) := e.base y
        have hinc : B.inclusion.map (Ebase.f j) =
            (((SmallEtale.toScheme B S hS).map f ⁻¹ᵁ W).ι) := by
          show (Ebase.map B.inclusion).f j = _
          rw [hmapEi j]
          exact openObjectι_map B S hS V _
        have hRangeEq :
            ((SmallEtale.toScheme B S hS).map (Rsmall.f i ≫ f)).base y =
              ((SmallEtale.toScheme B S hS).map f).base z.val := by
          rw [Functor.map_comp, hmapR, hArrow]
          show ((SmallEtale.toScheme B S hS).map f).base
              ((B.inclusion.map (Ebase.f j)).base (e.base y)) =
            ((SmallEtale.toScheme B S hS).map f).base z.val
          rw [hinc]
          rfl
        rw [hRangeEq]
        exact z.property
      simpa only [op_comp, F.obj.map_comp, ConcreteCategory.comp_apply] using
        restrict_zero_of_image_subset B S hS F U s W hW (Rsmall.X i) (Rsmall.f i ≫ f) hsubset
    exact section_zero_of_covering B S hS F V Rsmall hRsmall
      (F.obj.map f.op s) hzR

add_to_stacks 04FR "part (1): maximal open zero locus"
  AlgebraicGeometry.SmallEtale.zeroOpen
add_to_stacks 04FR "part (1): vanishing and maximality on Zariski opens"
  AlgebraicGeometry.SmallEtale.map_eq_zero_iff_le_zeroOpen

/-- An arrow of the small étale site whose image lies in a given Zariski open factors through
the corresponding object of the small étale site. -/
public def factorThroughOpenObject
    (V U : SmallEtale B S hS) (f : V ⟶ U)
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens)
    (hW : Set.range ((SmallEtale.toScheme B S hS).map f).base ⊆ W) :
    V ⟶ openObject B S hS U W := by
  let Vbase := B.obj (↑W : Scheme)
    (lt_of_le_of_lt (Scheme.size_coe_opens_le _ W) U.obj.left.property)
  let l : (SmallEtale.toScheme B S hS).obj V ⟶ (↑W : Scheme) :=
    IsOpenImmersion.lift W.ι ((SmallEtale.toScheme B S hS).map f)
      (by simpa only [Scheme.Opens.range_ι] using hW)
  have hlfac : l ≫ W.ι = (SmallEtale.toScheme B S hS).map f :=
    IsOpenImmersion.lift_fac W.ι ((SmallEtale.toScheme B S hS).map f)
      (by simpa only [Scheme.Opens.range_ι] using hW)
  let lbase : B.inclusion.obj V.obj.left ⟶ B.inclusion.obj Vbase := l
  let gbase : V.obj.left ⟶ Vbase := B.inclusion.preimage lbase
  have hOver : gbase ≫ (openObject B S hS U W).obj.hom = V.obj.hom := by
    apply B.inclusion.map_injective
    change B.inclusion.map gbase ≫
      B.inclusion.map (openObject B S hS U W).obj.hom =
        B.inclusion.map V.obj.hom
    rw [B.inclusion.map_preimage lbase]
    change lbase ≫
      B.inclusion.map (B.inclusion.preimage W.ι ≫ U.obj.hom) =
        B.inclusion.map V.obj.hom
    rw [Functor.map_comp, B.inclusion.map_preimage]
    change l ≫ W.ι ≫ B.inclusion.map U.obj.hom = B.inclusion.map V.obj.hom
    rw [← Category.assoc, hlfac]
    change B.inclusion.map f.hom.left ≫ B.inclusion.map U.obj.hom = _
    rw [← Functor.map_comp, Over.w]
  exact ⟨Over.homMk gbase hOver⟩

/-- The factorization of an arrow through the Zariski open containing its image recovers the
arrow. -/
public theorem factorThroughOpenObject_fac
    (V U : SmallEtale B S hS) (f : V ⟶ U)
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens)
    (hW : Set.range ((SmallEtale.toScheme B S hS).map f).base ⊆ W) :
    factorThroughOpenObject B S hS V U f W hW ≫ openObjectι B S hS U W = f := by
  let Vbase : B.Scheme := ⟨(↑W : Scheme),
    lt_of_le_of_lt (Scheme.size_coe_opens_le _ W) U.obj.left.property⟩
  let fscheme : B.inclusion.obj Vbase ⟶ B.inclusion.obj U.obj.left := W.ι
  have hW' : Set.range ((SmallEtale.toScheme B S hS).map f).base ⊆ Set.range W.ι.base := by
    simpa only [Scheme.Opens.range_ι] using hW
  let lbase : B.inclusion.obj V.obj.left ⟶ B.inclusion.obj Vbase :=
    IsOpenImmersion.lift W.ι ((SmallEtale.toScheme B S hS).map f) hW'
  apply (SmallEtale.inclusion B S hS).map_injective
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  show B.inclusion.map
      (B.inclusion.preimage lbase ≫ B.inclusion.preimage fscheme) =
    B.inclusion.map f.hom.left
  rw [Functor.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage]
  exact IsOpenImmersion.lift_fac W.ι ((SmallEtale.toScheme B S hS).map f) hW'

private theorem exists_covering_family_of_surjective_etale
    (V W : SmallEtale B S hS) (q : V ⟶ W)
    (hsurj : Function.Surjective ((SmallEtale.toScheme B S hS).map q).base) :
    ∃ E : PreZeroHypercover W,
      E.presieve₀ = Presieve.singleton q ∧
        SmallEtale.IsCovering B S hS ⟨W, E⟩ := by
  classical
  have hetale : Etale ((SmallEtale.toScheme B S hS).map q) := etale_toScheme_map B S hS q
  let qB := ((SmallEtale.inclusion B S hS).map q).left
  let C₀ : Covering B.Scheme := ⟨W.obj.left, PreZeroHypercover.singleton qB⟩
  have hEt : IsEtaleCovering C₀ := by
    show (PreZeroHypercover.singleton (B.inclusion.map qB)).presieve₀ ∈
      Scheme.etalePrecoverage (B.inclusion.obj W.obj.left)
    rw [PreZeroHypercover.presieve₀_singleton]
    show Presieve.singleton (B.inclusion.map qB) ∈
      Scheme.precoverage (@Etale) (B.inclusion.obj W.obj.left)
    rw [Scheme.singleton_mem_precoverage_iff (P := @Etale)]
    exact ⟨hsurj, hetale⟩
  obtain ⟨C₁, hC₁, hcomb⟩ := B.exists_covering_rep C₀ hEt
  obtain ⟨htarget, hcomb⟩ := hcomb
  rcases C₁ with ⟨T₁, E₁⟩
  cases htarget
  have hC₁et : (E₁.map B.inclusion).presieve₀ ∈
      Scheme.etalePrecoverage (B.inclusion.obj W.obj.left) := hC₁.1
  have hC₁maps : ∀ i, Etale (B.inclusion.map (E₁.f i)) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mp hC₁et).2
  let E : PreZeroHypercover W := {
    I₀ := E₁.I₀
    X := fun i => ⟨Over.mk (E₁.f i ≫ W.obj.hom), by
      show Etale (B.inclusion.map (E₁.f i ≫ W.obj.hom))
      rw [Functor.map_comp]
      let _ : Etale (B.inclusion.map (E₁.f i)) := hC₁maps i
      let _ : Etale (B.inclusion.map W.obj.hom) := W.property
      infer_instance⟩
    f := fun i => ObjectProperty.homMk (Over.homMk (E₁.f i) (by simp)) }
  have hEMap :
      (E.map (SmallEtale.inclusion B S hS)).map (Over.forget (B.obj S hS)) = E₁ := by
    cases E₁
    rfl
  have hEcover : SmallEtale.IsCovering B S hS ⟨W, E⟩ := by
    show B.IsCovering ⟨W.obj.left, (E.map (SmallEtale.inclusion B S hS)).map
      (Over.forget (B.obj S hS))⟩
    rw [hEMap]
    exact hC₁
  have hEpres : E.presieve₀ = Presieve.singleton q := by
    apply smallEtale_presieve_map_injective (B := B) (T := S) (hT := hS) (X := W)
    apply overForget_presieve_map_injective
    have hqMap :
        ((PreZeroHypercover.singleton q).map (SmallEtale.inclusion B S hS)).map
          (Over.forget (B.obj S hS)) = C₀.2 := by
      rfl
    calc
      Presieve.map (Over.forget (B.obj S hS))
          (Presieve.map (SmallEtale.inclusion B S hS) E.presieve₀) =
        Presieve.map (Over.forget (B.obj S hS))
          ((E.map (SmallEtale.inclusion B S hS)).presieve₀) := by
            rw [(PreZeroHypercover.presieve₀_map
              (F := SmallEtale.inclusion B S hS) E).symm]
      _ = ((E.map (SmallEtale.inclusion B S hS)).map
          (Over.forget (B.obj S hS))).presieve₀ := by
            rw [(PreZeroHypercover.presieve₀_map
              (F := Over.forget (B.obj S hS))
              (E.map (SmallEtale.inclusion B S hS))).symm]
      _ = E₁.presieve₀ := by rw [hEMap]
      _ = C₀.2.presieve₀ :=
        (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb).symm
      _ = ((PreZeroHypercover.singleton q).map (SmallEtale.inclusion B S hS)).presieve₀.map
          (Over.forget (B.obj S hS)) := by
            rw [← hqMap]
            rw [PreZeroHypercover.presieve₀_map
              (F := Over.forget (B.obj S hS))
              ((PreZeroHypercover.singleton q).map (SmallEtale.inclusion B S hS))]
      _ = Presieve.map (Over.forget (B.obj S hS))
          (Presieve.map (SmallEtale.inclusion B S hS) (Presieve.singleton q)) := by
            simp only [PreZeroHypercover.presieve₀_map,
              PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton]
  exact ⟨E, hEpres, hEcover⟩

private theorem eq_zero_of_surjective_etale_restriction
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (V W : SmallEtale B S hS) (q : V ⟶ W)
    (hsurj : Function.Surjective ((SmallEtale.toScheme B S hS).map q).base)
    (s : F.obj.obj (op W))
    (hzero : (F.obj.map q.op).hom s = 0) : s = 0 := by
  obtain ⟨E, hEpres, hEcover⟩ :=
    exists_covering_family_of_surjective_etale B S hS V W q hsurj
  refine section_zero_of_covering B S hS F W E hEcover s fun i => ?_
  have hg : Presieve.singleton q (E.f i) := by
    rw [← hEpres]
    exact E.presieve₀_f i
  cases hg
  simpa using hzero

/-- A section pulls back to zero along an arbitrary arrow of the small étale site precisely when
the image of that arrow is contained in its maximal Zariski open zero locus. -/
@[stacks 04FR "part (2): vanishing over the image", sga "2 XIV 1.8.2.1" "abelian, image criterion"]
public theorem map_eq_zero_iff_range_subset_zeroOpen
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U : SmallEtale B S hS) (σ : F.obj.obj (op U))
    (V : SmallEtale B S hS) (f : V ⟶ U) :
    F.obj.map f.op σ = 0 ↔
      Set.range ((SmallEtale.toScheme B S hS).map f).base ⊆
        (zeroOpen B S hS F U σ : Set ((SmallEtale.toScheme B S hS).obj U)) := by
  classical
  let T := (SmallEtale.toScheme B S hS).obj U
  let fS := (SmallEtale.toScheme B S hS).map f
  let Z := zeroOpen B S hS F U σ
  have heq {X : SmallEtale B S hS} (Q : V ⟶ X) (j : X ⟶ U) (h : Q ≫ j = f) :
      (F.obj.map f.op).hom σ = (F.obj.map Q.op).hom ((F.obj.map j.op).hom σ) := by
    rw [← h, op_comp, Functor.map_comp]
    rfl
  constructor
  · intro hσ
    let _ : Etale fS := etale_toScheme_map B S hS f
    let _ : UniversallyOpen fS := inferInstance
    let W : T.Opens := ⟨Set.range fS.base, fS.isOpenMap.isOpen_range⟩
    have hW : Set.range fS.base ⊆ W := Set.Subset.rfl
    let Q := factorThroughOpenObject B S hS V U f W hW
    let j : openObject B S hS U W ⟶ U := openObjectι B S hS U W
    have hfac : Q ≫ j = f := factorThroughOpenObject_fac B S hS V U f W hW
    have hqfac : (SmallEtale.toScheme B S hS).map Q ≫
        (SmallEtale.toScheme B S hS).map j = fS := by
      rw [← Functor.map_comp, hfac]
    have hqfacW : (SmallEtale.toScheme B S hS).map Q ≫ W.ι = fS := by
      calc
        _ = (SmallEtale.toScheme B S hS).map Q ≫
            (SmallEtale.toScheme B S hS).map j := by
              rw [openObjectι_map]
        _ = fS := hqfac
    have hsurj : Function.Surjective ((SmallEtale.toScheme B S hS).map Q).base := by
      intro y
      obtain ⟨x, hx⟩ : y.1 ∈ Set.range fS.base := y.2
      exact ⟨x, Subtype.ext ((congrArg (fun g : Scheme.Hom _ _ => g.base x) hqfacW).trans hx)⟩
    have hQzero : (F.obj.map Q.op).hom ((F.obj.map j.op).hom σ) = 0 :=
      (heq Q j hfac).symm.trans hσ
    have hJzero := eq_zero_of_surjective_etale_restriction B S hS F V
      (openObject B S hS U W) Q hsurj ((F.obj.map j.op).hom σ) hQzero
    have hJrange := (map_eq_zero_iff_le_zeroOpen
      B S hS F U σ (openObject B S hS U W) j).mp hJzero
    rintro _ ⟨a, rfl⟩
    have hpoint : (((SmallEtale.toScheme B S hS).map j).base
        (((SmallEtale.toScheme B S hS).map Q).base a)) = fS.base a := by
      have hpoint := congrArg (fun g : Scheme.Hom _ _ => g.base a) hqfac
      simpa only [Scheme.Hom.comp_base, TopCat.coe_comp,
        Function.comp_apply, Scheme.Hom.comp_apply] using hpoint
    exact hJrange (⟨((SmallEtale.toScheme B S hS).map Q).base a, hpoint⟩ :
      fS.base a ∈ ((SmallEtale.toScheme B S hS).map j).opensRange)
  · intro himage
    let W : T.Opens := Z
    have hW : Set.range fS.base ⊆ W := by simpa only [W] using himage
    let Q := factorThroughOpenObject B S hS V U f W hW
    let j : openObject B S hS U W ⟶ U := openObjectι B S hS U W
    have hfac : Q ≫ j = f := factorThroughOpenObject_fac B S hS V U f W hW
    have hJzero : (F.obj.map j.op).hom σ = 0 := by
      have hWle : ((SmallEtale.toScheme B S hS).map j).opensRange ≤ Z := by
        show Set.range ((SmallEtale.toScheme B S hS).map j).base ⊆ (Z : Set T)
        rw [openObjectι_map]
        show Set.range Z.ι ⊆ (Z : Set T)
        rw [Scheme.Opens.range_ι]
      exact (map_eq_zero_iff_le_zeroOpen
        B S hS F U σ (openObject B S hS U W) j).2 hWle
    rw [heq Q j hfac, hJzero, map_zero]

/-- The support of a section of an abelian étale sheaf is closed. -/
@[stacks 04FT "the support of a section is closed"]
public theorem isClosed_supportSection
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U : SmallEtale B S hS) (s : F.obj.obj (op U)) :
    IsClosed (supportSection B S hS F U s) :=
  (zeroOpen B S hS F U s).isOpen.isClosed_compl

/-- The support of a sum of sections is contained in the union of their supports. -/
@[stacks 04FT "the support of a sum of sections"]
public theorem supportSection_add_subset
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U : SmallEtale B S hS) (s s' : F.obj.obj (op U)) :
    supportSection B S hS F U (s + s') ⊆
      supportSection B S hS F U s ∪ supportSection B S hS F U s' := by
  intro x hx
  by_contra hnot
  change ¬ (x ∉ zeroOpen B S hS F U s ∨ x ∉ zeroOpen B S hS F U s') at hnot
  simp only [not_or, not_not] at hnot
  obtain ⟨hs, hs'⟩ := hnot
  let W := zeroOpen B S hS F U s ⊓ zeroOpen B S hS F U s'
  have hxW : x ∈ W := ⟨hs, hs'⟩
  let V := openObject B S hS U W
  let f := openObjectι B S hS U W
  have himage : ((SmallEtale.toScheme B S hS).map f).opensRange = W :=
    openObjectι_opensRange B S hS U W
  have hzero : F.obj.map f.op s = 0 :=
    (map_eq_zero_iff_le_zeroOpen B S hS F U s V f).2
      (by rw [himage]; exact inf_le_left)
  have hzero' : F.obj.map f.op s' = 0 :=
    (map_eq_zero_iff_le_zeroOpen B S hS F U s' V f).2
      (by rw [himage]; exact inf_le_right)
  have hsum_image :=
    (map_eq_zero_iff_le_zeroOpen B S hS F U (s + s') V f).1
      (by simp [map_add, hzero, hzero'])
  change x ∉ zeroOpen B S hS F U (s + s') at hx
  exact hx (hsum_image (by rw [himage]; exact hxW))

/-- A morphism of abelian sheaves cannot enlarge the support of a section. -/
@[stacks 04FT "the support under a morphism of sheaves"]
public theorem supportSection_map_subset
    (F G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (φ : F ⟶ G) (U : SmallEtale B S hS) (s : F.obj.obj (op U)) :
    supportSection B S hS G U (φ.hom.app (op U) s) ⊆ supportSection B S hS F U s := by
  have hzero : zeroOpen B S hS F U s ≤ zeroOpen B S hS G U (φ.hom.app (op U) s) := by
    unfold zeroOpen
    apply sSup_le
    rintro W ⟨V, f, hf, hW, hs⟩
    show (W : Set ((SmallEtale.toScheme B S hS).obj U)) ⊆
      (zeroOpen B S hS G U (φ.hom.app (op U) s) : Set _)
    rw [hW]
    exact (@map_eq_zero_iff_le_zeroOpen B S hS G U (φ.hom.app (op U) s) V f hf).mp (by
      calc
        _ = φ.hom.app (op V) (F.obj.map f.op s) :=
          (ConcreteCategory.congr_hom (φ.hom.naturality f.op) s).symm
        _ = 0 := by rw [hs, map_zero])
  exact fun _ hx hxF => hx (hzero hxF)

end AlgebraicGeometry.SmallEtale

end
