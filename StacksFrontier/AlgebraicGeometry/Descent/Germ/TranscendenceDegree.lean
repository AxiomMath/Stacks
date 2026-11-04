module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.SetTheory.Cardinal.ENat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Local

/-!
# Residue-field transcendence degree is étale local on germs

The transcendence degree of the extension of residue fields at the distinguished points of a
morphism of germs is unchanged by étale changes of source and target.

## Main definitions

* `AlgebraicGeometry.MorphismOfGerms.HasResidueFieldTranscendenceDegree` expresses a specified
  residue-field transcendence degree for a morphism of germs.

## Main results

* `AlgebraicGeometry.MorphismOfGerms.hasResidueFieldTranscendenceDegree_unique` states that the
  specified degree is determined by the morphism of germs.
* `AlgebraicGeometry.MorphismOfGerms.residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget`
  states étale locality on the source and target.

## Implementation notes

A representative of a germ morphism induces a map between residue fields at the distinguished
points. The property is expressed by the existence of a representative with the specified
transcendence degree, without choosing a representative in the definition. The parameter is
in `ℕ∞`, matching the finite degrees and the infinite value in the source.

## References

* [Stacks Project, Tag 04NK](https://stacks.math.columbia.edu/tag/04NK)
-/

@[expose] public section

namespace AlgebraicGeometry.MorphismOfGerms

open AlgebraicGeometry CategoryTheory

universe u


/-- A morphism of germs has the indicated transcendence degree between the
residue fields of its distinguished points. -/
public abbrev HasResidueFieldTranscendenceDegree (r : ℕ∞)
    {X S : GermOfScheme.{u}} (f : MorphismOfGerms X S) : Prop :=
  ∃ g : MorphismOfGerms.Representative X S,
    MorphismOfGerms.mk g = f ∧
      (let x : g.source.toScheme := ⟨X.point, g.mem_source⟩
       letI := ((S.scheme.residueFieldCongr g.map_point).inv ≫
         g.hom.residueFieldMap x).hom.toAlgebra
       Cardinal.toENat
         (Algebra.trdeg (S.scheme.residueField S.point)
           (g.source.toScheme.residueField x)) = r)

private theorem trdeg_eq_of_algebraic_square
    {K K' L L' : Type u} [Field K] [Field K'] [Field L] [Field L']
    (f : K →+* L) (f' : K' →+* L') (i : K →+* K') (j : L →+* L')
    (hsq : f'.comp i = j.comp f)
    (hi : letI : Algebra K K' := i.toAlgebra; Algebra.IsAlgebraic K K')
    (hj : letI : Algebra L L' := j.toAlgebra; Algebra.IsAlgebraic L L') :
    letI : Algebra K L := f.toAlgebra
    letI : Algebra K' L' := f'.toAlgebra
    Algebra.trdeg K L = Algebra.trdeg K' L' := by
  let : Algebra K L := f.toAlgebra
  let : Algebra K K' := i.toAlgebra
  let : Algebra K' L' := f'.toAlgebra
  let : Algebra L L' := j.toAlgebra
  let : Algebra K L' := (j.comp f).toAlgebra
  let : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K K' L' := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact congrArg (fun φ : K →+* L' => φ x) hsq.symm)
  have hleft := trdeg_add_eq K L (A := L')
  have hright := trdeg_add_eq K K' (A := L')
  let : Algebra.IsAlgebraic L L' := hj
  let : Algebra.IsAlgebraic K K' := hi
  have hzeroL : Algebra.trdeg L L' = 0 := trdeg_eq_zero
  have hzeroK : Algebra.trdeg K K' = 0 := trdeg_eq_zero
  rw [hzeroL, add_zero] at hleft
  rw [hzeroK, zero_add] at hright
  exact hleft.trans hright.symm

private theorem algebraic_of_ringEquiv_square
    {K K' L L' : Type u} [Field K] [Field K'] [Field L] [Field L']
    (i : K ≃+* K') (j : L' ≃+* L) (f : K' →+* L') (g : K →+* L)
    (hsq : g = j.toRingHom.comp (f.comp i.toRingHom))
    (hf : letI : Algebra K' L' := f.toAlgebra; Algebra.IsAlgebraic K' L') :
    letI : Algebra K L := g.toAlgebra
    Algebra.IsAlgebraic K L := by
  let : Algebra K' L' := f.toAlgebra
  let : Algebra K L := g.toAlgebra
  let : Algebra.IsAlgebraic K' L' := hf
  have hmap : f.comp i.toRingHom = j.symm.toRingHom.comp g := by
    ext x
    rw [hsq]
    simp
  exact Algebra.IsAlgebraic.of_ringHom_of_comp_eq i.toRingHom j.symm.toRingHom
    i.surjective j.symm.injective hmap

private noncomputable def openResidueFieldMapIso
    {X : Scheme.{u}} (U : X.Opens) (x : U) :
    X.residueField (U.ι x) ≃+* U.toScheme.residueField x := by
  letI : IsOpenImmersion U.ι := inferInstance
  letI : IsIso (U.ι.residueFieldMap x) :=
    AlgebraicGeometry.Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion U.ι x
  exact (asIso (U.ι.residueFieldMap x)).commRingCatIsoToRingEquiv

private noncomputable def representativeResidueFieldMap
    {X Y : GermOfScheme.{u}} (f : MorphismOfGerms.Representative X Y) :
    Y.scheme.residueField Y.point →+* X.scheme.residueField X.point := by
  let x : f.source.toScheme := ⟨X.point, f.mem_source⟩
  exact (openResidueFieldMapIso f.source x).symm.toRingHom.comp
    ((Y.scheme.residueFieldCongr f.map_point).inv ≫ f.hom.residueFieldMap x).hom

private noncomputable def normalizedResidueFieldMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    Y.residueField y →+* X.residueField x :=
  ((Y.residueFieldCongr h).inv ≫ f.residueFieldMap x).hom

private theorem normalizedResidueFieldMap_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (y : Y) (z : Z)
    (h₁ : f x = y) (h₂ : g y = z) :
    normalizedResidueFieldMap (f ≫ g) x z (by simp [h₁, h₂]) =
      (normalizedResidueFieldMap f x y h₁).comp
        (normalizedResidueFieldMap g y z h₂) := by
  subst h₁ h₂
  ext a
  simp [normalizedResidueFieldMap, Scheme.residueFieldMap_comp]

private noncomputable def openResidueFieldMapIsoAt
    {X : Scheme.{u}} (U : X.Opens) (x : U) (y : X) (h : U.ι x = y) :
    X.residueField y ≃+* U.toScheme.residueField x :=
  (X.residueFieldCongr h).commRingCatIsoToRingEquiv.symm.trans
    (openResidueFieldMapIso U x)

private theorem openResidueFieldMapIsoAt_toRingHom
    {X : Scheme.{u}} (U : X.Opens) (x : U) (y : X) (h : U.ι x = y) :
    (openResidueFieldMapIsoAt U x y h).toRingHom =
      normalizedResidueFieldMap U.ι x y h := by
  subst y
  ext z
  show (openResidueFieldMapIso U x).toRingHom z =
    (U.ι.residueFieldMap x).hom z
  rfl

private theorem normalizedResidueFieldMap_congr
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g)
    (x : X) (y : Y) (hf : f x = y) (hg : g x = y) :
    normalizedResidueFieldMap f x y hf = normalizedResidueFieldMap g x y hg := by
  subst g
  rfl

private theorem representativeResidueFieldMap_isAlgebraic_of_etale
    {X Y : GermOfScheme.{u}} (f : MorphismOfGerms.Representative X Y)
    [Etale f.hom] :
    letI : Algebra (Y.scheme.residueField Y.point) (X.scheme.residueField X.point) :=
      (representativeResidueFieldMap f).toAlgebra
    Algebra.IsAlgebraic (Y.scheme.residueField Y.point)
      (X.scheme.residueField X.point) := by
  let x : f.source.toScheme := ⟨X.point, f.mem_source⟩
  let K := Y.scheme.residueField Y.point
  let K' := Y.scheme.residueField (f.hom x)
  let L' := f.source.toScheme.residueField x
  let L := X.scheme.residueField X.point
  let i : K ≃+* K' := (Y.scheme.residueFieldCongr f.map_point).commRingCatIsoToRingEquiv.symm
  let j : L' ≃+* L := (openResidueFieldMapIso f.source x).symm
  let q : K' →+* L' := (f.hom.residueFieldMap x).hom
  let p : K →+* L := representativeResidueFieldMap f
  have hfinite : let : Algebra K' L' := q.toAlgebra; Algebra.IsAlgebraic K' L' := by
    let : Algebra K' L' := q.toAlgebra
    let : Module.Finite K' L' :=
      finite_residueField_of_etale_fibers f.hom (fun _ => inferInstance) x
    infer_instance
  simpa [K, K', L', L, p, q, i, j] using
    (algebraic_of_ringEquiv_square i j q p rfl hfinite)

private lemma residueFieldMap_normalized_congr
    {X Y : Scheme.{u}} (f : X ⟶ Y) {x x' : X} (h : x = x')
    {y : Y} (hx : f x = y) (hx' : f x' = y) :
    (Y.residueFieldCongr hx).inv ≫ f.residueFieldMap x ≫
        (X.residueFieldCongr h).hom =
      (Y.residueFieldCongr hx').inv ≫ f.residueFieldMap x' := by
  subst x'
  have : hx = hx' := Subsingleton.elim _ _
  subst hx'
  simp

private theorem trdeg_source_open_eq_ambient
    {X Y : GermOfScheme.{u}} (f : MorphismOfGerms.Representative X Y) :
    let x : f.source.toScheme := ⟨X.point, f.mem_source⟩
    letI := ((Y.scheme.residueFieldCongr f.map_point).inv ≫
      f.hom.residueFieldMap x).hom.toAlgebra
    letI := (representativeResidueFieldMap f).toAlgebra
    Algebra.trdeg (Y.scheme.residueField Y.point) (f.source.toScheme.residueField x) =
      Algebra.trdeg (Y.scheme.residueField Y.point) (X.scheme.residueField X.point) := by
  dsimp only
  let x : f.source.toScheme := ⟨X.point, f.mem_source⟩
  let : Algebra (Y.scheme.residueField Y.point) (f.source.toScheme.residueField x) :=
    (((Y.scheme.residueFieldCongr f.map_point).inv ≫
      f.hom.residueFieldMap x).hom).toAlgebra
  let : Algebra (Y.scheme.residueField Y.point) (X.scheme.residueField X.point) :=
    (representativeResidueFieldMap f).toAlgebra
  let e : f.source.toScheme.residueField x ≃ₐ[Y.scheme.residueField Y.point]
      X.scheme.residueField X.point :=
    { toRingEquiv := (openResidueFieldMapIso f.source x).symm
      commutes' _ := rfl }
  exact e.trdeg_eq


/-- Transposing a commuting square of ring homomorphisms along two ring isomorphisms. -/
private theorem symm_comp_eq_comp_symm {A B C D : Type*} [Semiring A] [Semiring B] [Semiring C]
    [Semiring D] (e : A ≃+* B) (e' : C ≃+* D) (a : B →+* D) (c : A →+* C)
    (h : a.comp e.toRingHom = e'.toRingHom.comp c) :
    e'.symm.toRingHom.comp a = c.comp e.symm.toRingHom := by
  ext z
  simpa using congrArg e'.symm (DFunLike.congr_fun h (e.symm z))

private theorem representativeResidueFieldMap_restrict
    {X Y : GermOfScheme.{u}} (f : MorphismOfGerms.Representative X Y)
    (U : X.scheme.Opens) (hxU : X.point ∈ U) (hU : U ≤ f.source) :
    representativeResidueFieldMap (restrictRepresentative f U hxU hU) =
      representativeResidueFieldMap f := by
  let xU : U.toScheme := ⟨X.point, hxU⟩
  let x₁ : f.source.toScheme := X.scheme.homOfLE hU xU
  let x₀ : f.source.toScheme := ⟨X.point, f.mem_source⟩
  have hLE : X.scheme.homOfLE hU ≫ f.source.ι = U.ι := by simp
  have hx : x₁ = x₀ := by
    apply Subtype.ext
    show f.source.ι (X.scheme.homOfLE hU xU) = X.point
    calc
      _ = (X.scheme.homOfLE hU ≫ f.source.ι) xU := rfl
      _ = U.ι xU := congrArg (fun k : U.toScheme ⟶ X.scheme => k xU) hLE
      _ = X.point := rfl
  have hbase₀ : f.source.ι x₀ = U.ι xU := by rfl
  have hbase : f.source.ι x₁ = U.ι xU :=
    congrArg (fun k : U.toScheme ⟶ X.scheme => k xU) hLE
  have hbaseEq : hbase = (congrArg f.source.ι hx).trans hbase₀ :=
    Subsingleton.elim _ _
  let cV := f.source.toScheme.residueFieldCongr hx
  let cX := X.scheme.residueFieldCongr (congrArg f.source.ι hx)
  let e₁ := openResidueFieldMapIso f.source x₁
  let e₀ := openResidueFieldMapIso f.source x₀
  let eU := openResidueFieldMapIso U xU
  let qU := (X.scheme.homOfLE hU).residueFieldMap xU
  have hraw : qU.hom.comp (f.source.ι.residueFieldMap x₁).hom =
      (U.ι.residueFieldMap xU).hom.comp
        (X.scheme.residueFieldCongr hbase).hom.hom := by
    have h := congrArg (fun m : CommRingCat.Hom _ _ => m.hom)
      (AlgebraicGeometry.Scheme.Hom.residueFieldMap_congr hLE xU)
    rw [Scheme.residueFieldMap_comp] at h
    exact h
  have hopen : (f.source.ι.residueFieldMap x₀).hom.comp cX.hom.hom =
      cV.hom.hom.comp (f.source.ι.residueFieldMap x₁).hom := by
    have h := congrArg (fun m : CommRingCat.Hom _ _ => m.hom)
      (AlgebraicGeometry.Scheme.Hom.residueFieldMap_congr' (f := f.source.ι) hx)
    exact h.symm
  have heU : qU.hom.comp e₁.toRingHom =
      eU.toRingHom.comp (X.scheme.residueFieldCongr hbase).hom.hom := by
    simpa [qU, e₁, eU, openResidueFieldMapIso] using hraw
  have heOpen : e₀.toRingHom.comp cX.hom.hom =
      cV.hom.hom.comp e₁.toRingHom := by
    simpa [e₀, e₁, openResidueFieldMapIso] using hopen
  have heUInv := symm_comp_eq_comp_symm e₁ eU qU.hom (X.scheme.residueFieldCongr hbase).hom.hom heU
  have heOpenInv := symm_comp_eq_comp_symm e₁ e₀ cV.hom.hom cX.hom.hom heOpen.symm
  have hq : (Y.scheme.residueFieldCongr
      ((congrArg f.hom hx).trans f.map_point)).inv ≫
      (X.scheme.homOfLE hU ≫ f.hom).residueFieldMap xU =
      ((Y.scheme.residueFieldCongr
        ((congrArg f.hom hx).trans f.map_point)).inv ≫
        f.hom.residueFieldMap x₁) ≫ qU := by
    rw [Scheme.residueFieldMap_comp]
    rfl
  have hq₀ : ((Y.scheme.residueFieldCongr
      ((congrArg f.hom hx).trans f.map_point)).inv ≫
      f.hom.residueFieldMap x₁) ≫ cV.hom =
      (Y.scheme.residueFieldCongr f.map_point).inv ≫
        f.hom.residueFieldMap x₀ := by
    simpa [cV] using residueFieldMap_normalized_congr f.hom hx
      ((congrArg f.hom hx).trans f.map_point) f.map_point
  have hcong : (X.scheme.residueFieldCongr hbase).hom.hom = cX.hom.hom := by
    rw [hbaseEq]
    congr 1
  let g : MorphismOfGerms.Representative X Y := {
    source := U
    mem_source := hxU
    hom := X.scheme.homOfLE hU ≫ f.hom
    map_point := by
      show f.hom (X.scheme.homOfLE hU ⟨X.point, hxU⟩) = Y.point
      rw [show X.scheme.homOfLE hU ⟨X.point, hxU⟩ =
        ⟨X.point, f.mem_source⟩ by apply Subtype.ext; simp]
      exact f.map_point
  }
  have hg : g = restrictRepresentative f U hxU hU := rfl
  have hpm : g.map_point =
      ((congrArg f.hom hx).trans f.map_point) := Subsingleton.elim _ _
  apply RingHom.ext
  intro z
  let qV₁ := (Y.scheme.residueFieldCongr
    ((congrArg f.hom hx).trans f.map_point)).inv ≫ f.hom.residueFieldMap x₁
  let qV₀ := (Y.scheme.residueFieldCongr f.map_point).inv ≫
    f.hom.residueFieldMap x₀
  let w := qV₁.hom z
  have h1 := congrArg (fun k => k w) heUInv
  have h2 := congrArg (fun k => k w) heOpenInv
  have h3 := congrArg (fun k : CommRingCat.Hom _ _ => k.hom z) hq₀
  rw [← hg]
  dsimp only [representativeResidueFieldMap, g]
  rw [hpm]
  show eU.symm.toRingHom
      ((CommRingCat.Hom.hom
        ((Y.scheme.residueFieldCongr
          ((congrArg f.hom hx).trans f.map_point)).inv ≫
          (X.scheme.homOfLE hU ≫ f.hom).residueFieldMap xU)) z) =
    e₀.symm.toRingHom (qV₀.hom z)
  have hql := congrArg (fun k : CommRingCat.Hom _ _ => k.hom z) hq
  have hql' :
      (CommRingCat.Hom.hom
        ((Y.scheme.residueFieldCongr
          ((congrArg f.hom hx).trans f.map_point)).inv ≫
          (X.scheme.homOfLE hU ≫ f.hom).residueFieldMap xU)) z =
        qU.hom w := by
    simpa [qV₁, w, Category.assoc] using hql
  have h1' : eU.symm.toRingHom (qU.hom w) =
      (X.scheme.residueFieldCongr hbase).hom.hom (e₁.symm.toRingHom w) := by
    simpa [RingHom.comp_apply] using h1
  have h2' : e₀.symm.toRingHom (cV.hom.hom w) =
      cX.hom.hom (e₁.symm.toRingHom w) := by
    simpa [RingHom.comp_apply] using h2
  have hmid : (X.scheme.residueFieldCongr hbase).hom.hom
      (e₁.symm.toRingHom w) = cX.hom.hom (e₁.symm.toRingHom w) :=
    congrArg (fun k : _ →+* _ => k (e₁.symm.toRingHom w)) hcong
  have h3' : cV.hom.hom w = qV₀.hom z := by
    simpa [qV₁, qV₀, w, Category.assoc] using h3
  exact (congrArg eU.symm.toRingHom hql').trans
    (h1'.trans (hmid.trans (h2'.symm.trans
      (congrArg e₀.symm.toRingHom h3'))))

private theorem representativeResidueFieldMap_compRepresentative
    {X Y Z : GermOfScheme.{u}}
    (f : MorphismOfGerms.Representative X Y)
    (g : MorphismOfGerms.Representative Y Z) :
    representativeResidueFieldMap
      (compRepresentative f g) =
      (representativeResidueFieldMap f).comp (representativeResidueFieldMap g) := by
  let P := f.hom ⁻¹ᵁ g.source
  let W := f.source.ι ''ᵁ P
  let xF : f.source.toScheme := ⟨X.point, f.mem_source⟩
  have hxP : xF ∈ P := by
    show f.hom xF ∈ g.source
    rw [f.map_point]
    exact g.mem_source
  let xP : P.toScheme := ⟨xF, hxP⟩
  let xG : g.source.toScheme := ⟨Y.point, g.mem_source⟩
  let xW : W.toScheme := ⟨X.point, ⟨xF, hxP, rfl⟩⟩
  let e : W.toScheme ⟶ P.toScheme := (f.source.ι.isoImage P).inv
  let r : P.toScheme ⟶ g.source.toScheme := f.hom ∣_ g.source
  have hSquareHom : r ≫ g.source.ι = P.ι ≫ f.hom := by
    simp [r, P]
  have hImageHom : e ≫ P.ι ≫ f.source.ι = W.ι := by
    calc
      _ = (f.source.ι.isoImage P).inv ≫ P.ι ≫ f.source.ι := rfl
      _ = X.scheme.homOfLE (f.source.ι_image_le P) ≫ f.source.ι := by
        rw [← Category.assoc, Scheme.Opens.isoImage_ι_inv_ι]
      _ = W.ι := by simp [W, P]
  have he : e xW = xP := by
    apply Subtype.ext
    apply Subtype.ext
    show f.source.ι (P.ι (e xW)) = W.ι xW
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun k : W.toScheme ⟶ X.scheme => k xW) hImageHom
  have hpx : P.ι xP = xF := Subtype.ext rfl
  have hfpt : f.source.ι xF = X.point := rfl
  have hgpt : g.source.ι xG = Y.point := rfl
  have hr : r xP = xG := by
    apply Subtype.ext
    calc
      g.source.ι (r xP) = f.hom (P.ι xP) := by
        simpa only [Scheme.Hom.comp_apply] using
          congrArg (fun k : P.toScheme ⟶ Y.scheme => k xP) hSquareHom
      _ = Y.point := by rw [hpx, f.map_point]
  let nW := normalizedResidueFieldMap W.ι xW X.point rfl
  let nF := normalizedResidueFieldMap f.source.ι xF X.point hfpt
  let nP := normalizedResidueFieldMap P.ι xP xF hpx
  let nG := normalizedResidueFieldMap g.source.ι xG Y.point hgpt
  let nE := normalizedResidueFieldMap e xW xP he
  let nR := normalizedResidueFieldMap r xP xG hr
  let nf := normalizedResidueFieldMap f.hom xF Y.point f.map_point
  let ng := normalizedResidueFieldMap g.hom xG Z.point g.map_point
  let eW := openResidueFieldMapIsoAt W xW X.point rfl
  let eF := openResidueFieldMapIsoAt f.source xF X.point hfpt
  let eG := openResidueFieldMapIsoAt g.source xG Y.point hgpt
  have hW : eW.toRingHom = nW :=
    openResidueFieldMapIsoAt_toRingHom W xW X.point rfl
  have hF : eF.toRingHom = nF :=
    openResidueFieldMapIsoAt_toRingHom f.source xF X.point hfpt
  have hG : eG.toRingHom = nG :=
    openResidueFieldMapIsoAt_toRingHom g.source xG Y.point hgpt
  have hSquare : nR.comp nG = nP.comp nf := by
    calc
      _ = normalizedResidueFieldMap (r ≫ g.source.ι) xP Y.point
          (by rw [Scheme.Hom.comp_apply, hr, hgpt]) :=
        (normalizedResidueFieldMap_comp r g.source.ι xP xG Y.point hr hgpt).symm
      _ = normalizedResidueFieldMap (P.ι ≫ f.hom) xP Y.point
          (by rw [Scheme.Hom.comp_apply, hpx, f.map_point]) :=
        normalizedResidueFieldMap_congr hSquareHom xP Y.point _ _
      _ = _ := normalizedResidueFieldMap_comp P.ι f.hom xP xF Y.point hpx f.map_point
  have hImage : (nE.comp nP).comp nF = nW := by
    have hEP : normalizedResidueFieldMap (e ≫ P.ι) xW xF
        (by rw [Scheme.Hom.comp_apply, he, hpx]) = nE.comp nP :=
      normalizedResidueFieldMap_comp e P.ι xW xP xF he hpx
    have hEPpt : (e ≫ P.ι) xW = xF := by
      rw [Scheme.Hom.comp_apply, he, hpx]
    have hEPF : normalizedResidueFieldMap ((e ≫ P.ι) ≫ f.source.ι)
        xW X.point (by rw [Scheme.Hom.comp_apply, hEPpt, hfpt]) =
        (normalizedResidueFieldMap (e ≫ P.ι) xW xF hEPpt).comp nF :=
      normalizedResidueFieldMap_comp (e ≫ P.ι) f.source.ι xW xF X.point hEPpt hfpt
    calc
      _ = (normalizedResidueFieldMap (e ≫ P.ι) xW xF hEPpt).comp nF := by
        rw [← hEP]
      _ = normalizedResidueFieldMap ((e ≫ P.ι) ≫ f.source.ι) xW X.point
          (by rw [Scheme.Hom.comp_apply, hEPpt, hfpt]) := hEPF.symm
      _ = nW := normalizedResidueFieldMap_congr hImageHom xW X.point _ _
  have hImageInv : (eW.symm.toRingHom.comp nE).comp nP = eF.symm.toRingHom := by
    simpa [RingHom.comp_assoc] using symm_comp_eq_comp_symm eF eW (nE.comp nP) (RingHom.id _)
      (by rw [hW, hF, ← hImage]; rfl)
  let c := compRepresentative f g
  have hER : (e ≫ r) xW = xG := by simp [he, hr]
  have hNormC : normalizedResidueFieldMap c.hom xW Z.point c.map_point =
      (nE.comp nR).comp ng := by
    show normalizedResidueFieldMap ((e ≫ r) ≫ g.hom) xW Z.point _ = _
    calc
      _ = (normalizedResidueFieldMap (e ≫ r) xW xG hER).comp ng :=
        normalizedResidueFieldMap_comp (e ≫ r) g.hom xW xG Z.point hER g.map_point
      _ = (nE.comp nR).comp ng := by
        rw [normalizedResidueFieldMap_comp e r xW xP xG he hr]
  have hpc : representativeResidueFieldMap c =
      eW.symm.toRingHom.comp ((nE.comp nR).comp ng) := by
    show eW.symm.toRingHom.comp
      (normalizedResidueFieldMap c.hom xW Z.point c.map_point) = _
    rw [hNormC]
  have hpf : representativeResidueFieldMap f = eF.symm.toRingHom.comp nf := rfl
  have hpg : representativeResidueFieldMap g = eG.symm.toRingHom.comp ng := rfl
  have hMiddle : nR.comp ng = (((nP.comp nf).comp eG.symm.toRingHom).comp ng) := by
    ext z
    have hz := congrArg (fun k : Y.scheme.residueField Y.point →+*
        P.toScheme.residueField xP => k (eG.symm (ng z))) hSquare
    rw [← hG] at hz
    simp only [RingHom.comp_apply] at hz
    have heG : eG.toRingHom (eG.symm (ng z)) = ng z := eG.apply_symm_apply _
    rw [heG] at hz
    change nR (ng z) = nP (nf (eG.symm (ng z))) at hz
    exact hz
  calc
    representativeResidueFieldMap c = (eW.symm.toRingHom.comp nE).comp
        (nR.comp ng) := hpc
    _ = (eW.symm.toRingHom.comp nE).comp
        (((nP.comp nf).comp eG.symm.toRingHom).comp ng) := by rw [hMiddle]
    _ = ((eF.symm.toRingHom.comp nf).comp eG.symm.toRingHom).comp ng := by
      have hh := congrArg (fun k : f.source.toScheme.residueField xF →+*
          X.scheme.residueField X.point => k.comp
            (nf.comp (eG.symm.toRingHom.comp ng))) hImageInv
      simpa [RingHom.comp_assoc] using hh
    _ = (representativeResidueFieldMap f).comp
        (representativeResidueFieldMap g) := by
      rw [hpf, hpg]
      simp [RingHom.comp_assoc]

private theorem representativeResidueFieldMap_eq_of_agreeNear
    {X Y : GermOfScheme.{u}} {f g : MorphismOfGerms.Representative X Y}
    (h : f.AgreeNear g) : representativeResidueFieldMap f =
      representativeResidueFieldMap g := by
  obtain ⟨W, hxW, hWf, hWg, hhom⟩ := h
  let xW : W.toScheme := ⟨X.point, hxW⟩
  let mF := X.scheme.homOfLE hWf ≫ f.hom
  let mG := X.scheme.homOfLE hWg ≫ g.hom
  let fW := restrictRepresentative f W hxW hWf
  let gW := restrictRepresentative g W hxW hWg
  have pF : mF xW = Y.point := fW.map_point
  have pG : mG xW = Y.point := gW.map_point
  have hAt : mF xW = mG xW := congrArg (fun k : W.toScheme ⟶ Y.scheme => k xW) hhom
  have hp : pF = hAt.trans pG := Subsingleton.elim _ _
  have hIso : (Y.scheme.residueFieldCongr pF).inv ≫
      (Y.scheme.residueFieldCongr hAt).hom =
      (Y.scheme.residueFieldCongr pG).inv := by
    rw [hp]
    have hcomp : Y.scheme.residueFieldCongr hAt ≪≫
        Y.scheme.residueFieldCongr pG =
        Y.scheme.residueFieldCongr (hAt.trans pG) :=
      Scheme.residueFieldCongr_trans hAt pG
    have hinv := congrArg (fun e : _ ≅ _ => e.inv) hcomp
    rw [← hinv]
    simp
  have hmap : mF.residueFieldMap xW =
      (Y.scheme.residueFieldCongr hAt).hom ≫ mG.residueFieldMap xW := by
    simpa [mF, mG] using Scheme.Hom.residueFieldMap_congr hhom xW
  have hnorm : (Y.scheme.residueFieldCongr pF).inv ≫
      mF.residueFieldMap xW =
      (Y.scheme.residueFieldCongr pG).inv ≫ mG.residueFieldMap xW := by
    calc
      _ = (Y.scheme.residueFieldCongr pF).inv ≫
          ((Y.scheme.residueFieldCongr hAt).hom ≫ mG.residueFieldMap xW) := by rw [hmap]
      _ = ((Y.scheme.residueFieldCongr pF).inv ≫
          (Y.scheme.residueFieldCongr hAt).hom) ≫ mG.residueFieldMap xW := by simp
      _ = (Y.scheme.residueFieldCongr pG).inv ≫ mG.residueFieldMap xW := by rw [hIso]
  have hmaps : representativeResidueFieldMap fW =
      representativeResidueFieldMap gW := by
    apply RingHom.ext
    intro z
    dsimp only [representativeResidueFieldMap, fW, gW]
    show ((openResidueFieldMapIso W xW).symm.toRingHom.comp
      ((Y.scheme.residueFieldCongr pF).inv ≫
        mF.residueFieldMap xW).hom) z =
      ((openResidueFieldMapIso W xW).symm.toRingHom.comp
        ((Y.scheme.residueFieldCongr pG).inv ≫
          mG.residueFieldMap xW).hom) z
    rw [hnorm]
  rw [← representativeResidueFieldMap_restrict f W hxW hWf,
    ← representativeResidueFieldMap_restrict g W hxW hWg]
  exact hmaps

private noncomputable def representativeAmbientTrdeg
    {X Y : GermOfScheme.{u}} (f : MorphismOfGerms.Representative X Y) : Cardinal :=
  letI : Algebra (Y.scheme.residueField Y.point) (X.scheme.residueField X.point) :=
    (representativeResidueFieldMap f).toAlgebra
  Algebra.trdeg (Y.scheme.residueField Y.point) (X.scheme.residueField X.point)

private theorem hasResidueFieldTranscendenceDegree_mk_iff
    (r : ℕ∞) {X Y : GermOfScheme.{u}}
    (f : MorphismOfGerms.Representative X Y) :
    HasResidueFieldTranscendenceDegree r (MorphismOfGerms.mk f) ↔
      Cardinal.toENat (representativeAmbientTrdeg f) = r := by
  constructor
  · rintro ⟨g, hg, hdeg⟩
    have htr : representativeAmbientTrdeg g = representativeAmbientTrdeg f := by
      unfold representativeAmbientTrdeg
      rw [representativeResidueFieldMap_eq_of_agreeNear (MorphismOfGerms.mk_eq_mk_iff.mp hg)]
    rw [← htr]
    exact (congrArg Cardinal.toENat (trdeg_source_open_eq_ambient g)).symm.trans hdeg
  · exact fun hdeg =>
      ⟨f, rfl, (congrArg Cardinal.toENat (trdeg_source_open_eq_ambient f)).trans hdeg⟩

/-- The residue-field transcendence degree of a morphism of germs is determined by that
morphism: at most one value in `ℕ∞` satisfies
`AlgebraicGeometry.MorphismOfGerms.HasResidueFieldTranscendenceDegree`. -/
public theorem hasResidueFieldTranscendenceDegree_unique {r₁ r₂ : ℕ∞}
    {X Y : GermOfScheme.{u}} {f : MorphismOfGerms X Y}
    (h₁ : HasResidueFieldTranscendenceDegree r₁ f)
    (h₂ : HasResidueFieldTranscendenceDegree r₂ f) : r₁ = r₂ := by
  obtain ⟨g, rfl⟩ := MorphismOfGerms.exists_rep f
  exact ((hasResidueFieldTranscendenceDegree_mk_iff r₁ g).mp h₁).symm.trans
    ((hasResidueFieldTranscendenceDegree_mk_iff r₂ g).mp h₂)

/-- **Stacks Project, Tag 04NK.** Residue-field transcendence degree at a
point is étale local on the source and target of a morphism of germs. -/
@[stacks 04NK]
public theorem residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget
    (r : ℕ∞) :
    IsEtaleLocalOnSourceAndTarget
      (@HasResidueFieldTranscendenceDegree.{u} r) := by
  refine ⟨?_⟩
  intro U' U V' V a b h' h ha hb hsq
  obtain ⟨fh', hfh'⟩ := MorphismOfGerms.exists_rep h'
  obtain ⟨fh, hfh⟩ := MorphismOfGerms.exists_rep h
  obtain ⟨ea, hea, heta⟩ := ha
  obtain ⟨eb, heb, hteb⟩ := hb
  have hmk : MorphismOfGerms.mk (compRepresentative fh' eb) =
      MorphismOfGerms.mk (compRepresentative ea fh) := by
    rwa [← comp_mk, ← comp_mk, hfh', heb, hea, hfh]
  have hsquare :
      (representativeResidueFieldMap fh').comp (representativeResidueFieldMap eb) =
      (representativeResidueFieldMap ea).comp (representativeResidueFieldMap fh) := by
    rw [← representativeResidueFieldMap_compRepresentative,
      ← representativeResidueFieldMap_compRepresentative]
    exact representativeResidueFieldMap_eq_of_agreeNear (MorphismOfGerms.mk_eq_mk_iff.mp hmk)
  have : Etale eb.hom := hteb
  have : Etale ea.hom := heta
  have hi := representativeResidueFieldMap_isAlgebraic_of_etale eb
  have hj := representativeResidueFieldMap_isAlgebraic_of_etale ea
  have htr := trdeg_eq_of_algebraic_square
    (representativeResidueFieldMap fh) (representativeResidueFieldMap fh')
    (representativeResidueFieldMap eb) (representativeResidueFieldMap ea)
    hsquare hi hj
  rw [← hfh, ← hfh', hasResidueFieldTranscendenceDegree_mk_iff,
    hasResidueFieldTranscendenceDegree_mk_iff]
  have htr' : Cardinal.toENat (representativeAmbientTrdeg fh) =
      Cardinal.toENat (representativeAmbientTrdeg fh') := by
    simpa [representativeAmbientTrdeg] using congrArg Cardinal.toENat htr
  rw [htr']

end AlgebraicGeometry.MorphismOfGerms

end
