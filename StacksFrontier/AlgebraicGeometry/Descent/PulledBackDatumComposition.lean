module

public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityBaseLocal

/-!
# Pulling a descent datum back along a composite of morphisms of families

Let `𝒳 ⟶ 𝒴 ⟶ 𝒵` be morphisms of families of schemes with fixed target, over morphisms
`R ⟶ T ⟶ W` of the base schemes, and let `D` be a descent datum relative to `𝒵`. Pulling `D`
back to `𝒴` and then to `𝒳` gives the same descent datum relative to `𝒳`, up to canonical
isomorphism, as pulling it back along the composite: the component at `i` is the iterated fibre
product `(D_{a} ×_{𝒵_a} 𝒴_{p}) ×_{𝒴_p} 𝒳_i` on one side and the fibre product
`D_{a} ×_{𝒵_a} 𝒳_i` along the composite on the other.

## Main definitions

* `AlgebraicGeometry.DescentData.homOfComponents` and
  `AlgebraicGeometry.DescentData.isoOfComponents` build a morphism, respectively an isomorphism,
  of descent data out of morphisms, respectively isomorphisms, of the components whose
  compatibility with the gluing isomorphisms is read on the literal fibre products.
* `AlgebraicGeometry.MorphismOfSchemeFamilies.pulledBackDatumCompObjIso` is the identification
  of the components of the two pulled-back data.

## Main results

* `AlgebraicGeometry.MorphismOfSchemeFamilies.pulledBackDatumCompIso`: **pulling a descent datum
  back along two morphisms of families in succession is pulling it back along their composite.**

## References

* [Stacks Project, Tag 02VS](https://stacks.math.columbia.edu/tag/02VS)
* [Stacks Project, Tag 02VT](https://stacks.math.columbia.edu/tag/02VT)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

namespace DescentData

variable {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}

/-- **A morphism of descent data read on the literal fibre products.** Morphisms of the
components whose induced maps on the sources and targets of the gluing isomorphisms commute with
them assemble into a morphism of descent data. -/
def homOfComponents {D E : DescentData f} (u : ∀ i, D.obj i ⟶ E.obj i)
    (hu : ∀ i j, srcGluingMap u i j ≫ (E.gluingPullbackIso i j).hom =
      (D.gluingPullbackIso i j).hom ≫ tgtGluingMap u i j) :
    D ⟶ E where
  hom := u
  comm i j := (comm_iff_gluingPullback u i j).mp (hu i j)

/-- The components of `homOfComponents u hu` are the morphisms `u i`. -/
@[simp]
lemma homOfComponents_hom {D E : DescentData f} (u : ∀ i, D.obj i ⟶ E.obj i)
    (hu : ∀ i j, srcGluingMap u i j ≫ (E.gluingPullbackIso i j).hom =
      (D.gluingPullbackIso i j).hom ≫ tgtGluingMap u i j) (i : ι) :
    (homOfComponents u hu).hom i = u i := rfl

/-- **An isomorphism of descent data read on the literal fibre products.** Isomorphisms of the
components whose induced maps on the sources and targets of the gluing isomorphisms commute with
them assemble into an isomorphism of descent data. -/
def isoOfComponents {D E : DescentData f} (e : ∀ i, D.obj i ≅ E.obj i)
    (he : ∀ i j, srcGluingMap (fun i ↦ (e i).hom) i j ≫ (E.gluingPullbackIso i j).hom =
      (D.gluingPullbackIso i j).hom ≫ tgtGluingMap (fun i ↦ (e i).hom) i j) :
    D ≅ E where
  hom := homOfComponents (fun i ↦ (e i).hom) he
  inv :=
    { hom := fun i ↦ (e i).inv
      comm := gluing_comm_inv (homOfComponents (fun i ↦ (e i).hom) he) e fun _ ↦ rfl }
  hom_inv_id := hom_ext fun i ↦ (e i).hom_inv_id
  inv_hom_id := hom_ext fun i ↦ (e i).inv_hom_id

/-- The components of the forward morphism of `isoOfComponents e he` are the morphisms
`(e i).hom`. -/
@[simp]
lemma isoOfComponents_hom_hom {D E : DescentData f} (e : ∀ i, D.obj i ≅ E.obj i)
    (he : ∀ i j, srcGluingMap (fun i ↦ (e i).hom) i j ≫ (E.gluingPullbackIso i j).hom =
      (D.gluingPullbackIso i j).hom ≫ tgtGluingMap (fun i ↦ (e i).hom) i j) (i : ι) :
    (isoOfComponents e he).hom.hom i = (e i).hom := rfl

/-- The components of the inverse morphism of `isoOfComponents e he` are the morphisms
`(e i).inv`. -/
@[simp]
lemma isoOfComponents_inv_hom {D E : DescentData f} (e : ∀ i, D.obj i ≅ E.obj i)
    (he : ∀ i j, srcGluingMap (fun i ↦ (e i).hom) i j ≫ (E.gluingPullbackIso i j).hom =
      (D.gluingPullbackIso i j).hom ≫ tgtGluingMap (fun i ↦ (e i).hom) i j) (i : ι) :
    (isoOfComponents e he).inv.hom i = (e i).inv := rfl

end DescentData

namespace MorphismOfSchemeFamilies

variable {R T W : Scheme.{u}} {𝒳 : PreZeroHypercover.{u} R} {𝒴 : PreZeroHypercover.{u} T}
  {𝒵 : PreZeroHypercover.{u} W} {g : R ⟶ T} {h : T ⟶ W} {k : R ⟶ W}

attribute [local implicit_reducible] CategoryTheory.PreZeroHypercover.HomOver.comp

/-- The identification of a component of a pulled-back datum with its chosen fibre product is
the identity on underlying schemes. -/
private lemma objIso_hom_left_comp (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) {Z : Scheme.{u}}
    (p : ((Over.pullback (F.familyHom.h₀ i)).obj (D.obj (F.familyHom.s₀ i))).left ⟶ Z) :
    (pulledBackDatumObjIso F D i).hom.left ≫ p = p :=
  Category.id_comp p

/-- Two morphisms into a component of a pulled-back datum agree as soon as they agree after the
projection onto the component of the original datum and after the structure morphism. -/
private lemma hom_ext_objIso (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (j : F.sourceFamily.I₀) {Z : Scheme.{u}}
    {a b : Z ⟶ ((pulledBackDatum F D).obj j).left}
    (h₁ : a ≫ (pulledBackDatumObjIso F D j).hom.left ≫
          pullback.fst (D.obj (F.familyHom.s₀ j)).hom (F.familyHom.h₀ j) =
        b ≫ (pulledBackDatumObjIso F D j).hom.left ≫
          pullback.fst (D.obj (F.familyHom.s₀ j)).hom (F.familyHom.h₀ j))
    (h₂ : a ≫ ((pulledBackDatum F D).obj j).hom = b ≫ ((pulledBackDatum F D).obj j).hom) :
    a = b := by
  simp only [objIso_hom_left_comp] at h₁
  exact pullback.hom_ext h₁ h₂

/-- The comparison map on the sources of the gluing isomorphisms of a pulled-back datum
projects to the chosen fibre product of the component at the first index. -/
@[reassoc]
public lemma pulledBackDatumSourceMap_comp_fst (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    pulledBackDatumSourceMap F D i j ≫
        pullback.fst ((D.obj (F.familyHom.s₀ i)).hom ≫
          F.targetFamily.f (F.familyHom.s₀ i)) (F.targetFamily.f (F.familyHom.s₀ j)) =
      pullback.fst (((pulledBackDatum F D).obj i).hom ≫ F.sourceFamily.f i)
          (F.sourceFamily.f j) ≫
        (pulledBackDatumObjIso F D i).hom.left ≫
        pullback.fst (D.obj (F.familyHom.s₀ i)).hom (F.familyHom.h₀ i) :=
  pullback.lift_fst _ _ _

/-- The comparison map on the sources of the gluing isomorphisms of a pulled-back datum
projects to the member of the target family at the second index. -/
@[reassoc]
public lemma pulledBackDatumSourceMap_comp_snd (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    pulledBackDatumSourceMap F D i j ≫
        pullback.snd ((D.obj (F.familyHom.s₀ i)).hom ≫
          F.targetFamily.f (F.familyHom.s₀ i)) (F.targetFamily.f (F.familyHom.s₀ j)) =
      pullback.snd (((pulledBackDatum F D).obj i).hom ≫ F.sourceFamily.f i)
          (F.sourceFamily.f j) ≫ F.familyHom.h₀ j :=
  pullback.lift_snd _ _ _

/-- The comparison map on the targets of the gluing isomorphisms of a pulled-back datum
projects to the chosen fibre product of the component at the second index. -/
@[reassoc]
public lemma pulledBackDatumTargetMap_comp_snd (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    pulledBackDatumTargetMap F D i j ≫
        pullback.snd (F.targetFamily.f (F.familyHom.s₀ i))
          ((D.obj (F.familyHom.s₀ j)).hom ≫ F.targetFamily.f (F.familyHom.s₀ j)) =
      pullback.snd (F.sourceFamily.f i)
          (((pulledBackDatum F D).obj j).hom ≫ F.sourceFamily.f j) ≫
        (pulledBackDatumObjIso F D j).hom.left ≫
        pullback.fst (D.obj (F.familyHom.s₀ j)).hom (F.familyHom.h₀ j) :=
  pullback.lift_snd _ _ _

/-- The gluing isomorphism of a pulled-back datum, read through the projection of the component
at the second index onto the component of the original datum. -/
@[reassoc]
private lemma gluing_snd_fst (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫
        pullback.snd (F.sourceFamily.f i)
          (((pulledBackDatum F D).obj j).hom ≫ F.sourceFamily.f j) ≫
        (pulledBackDatumObjIso F D j).hom.left ≫
        pullback.fst (D.obj (F.familyHom.s₀ j)).hom (F.familyHom.h₀ j) =
      pulledBackDatumSourceMap F D i j ≫
        (D.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ j)).hom ≫
        pullback.snd (F.targetFamily.f (F.familyHom.s₀ i))
          ((D.obj (F.familyHom.s₀ j)).hom ≫
            F.targetFamily.f (F.familyHom.s₀ j)) := by
  have key := congrArg (fun q ↦ q ≫ pullback.snd (F.targetFamily.f (F.familyHom.s₀ i))
      ((D.obj (F.familyHom.s₀ j)).hom ≫ F.targetFamily.f (F.familyHom.s₀ j)))
    (pulledBackDatum_gluing F D i j)
  simpa only [Category.assoc, pulledBackDatumTargetMap_comp_snd] using key

/-- **The components of the two pulled-back data agree.** The component at `i` of the datum
obtained by pulling `D` back along `ψ` and then along `φ` is the iterated fibre product
`(D_{ψ(φ(i))} ×_{𝒵} 𝒴_{φ(i)}) ×_{𝒴} 𝒳_i`, and the component at `i` of the pullback along the
composite is `D_{ψ(φ(i))} ×_{𝒵} 𝒳_i`; the two are identified by collapsing the iterated fibre
product. -/
def pulledBackDatumCompObjIso (φ : 𝒳.HomOver 𝒴 g) (ψ : 𝒴.HomOver 𝒵 h) (hk : g ≫ h = k)
    (D : DescentData 𝒵.f) (i : 𝒳.I₀) :
    (pulledBackDatum (ofHomOver 𝒳 𝒴 g φ)
        (pulledBackDatum (ofHomOver 𝒴 𝒵 h ψ) D)).obj i ≅
      (pulledBackDatum (ofHomOver 𝒳 𝒵 k (φ.comp ψ hk)) D).obj i :=
  pullbackCompObjIso (D.obj (ψ.s₀ (φ.s₀ i))) (φ.h₀ i) (ψ.h₀ (φ.s₀ i))
    (φ.h₀ i ≫ ψ.h₀ (φ.s₀ i)) rfl

/-- The identification of the components of the two pulled-back data preserves the projection
onto the component of the original datum. -/
@[reassoc]
private lemma compObjIso_fst (φ : 𝒳.HomOver 𝒴 g) (ψ : 𝒴.HomOver 𝒵 h) (hk : g ≫ h = k)
    (D : DescentData 𝒵.f) (i : 𝒳.I₀) :
    (pulledBackDatumCompObjIso φ ψ hk D i).hom.left ≫
        (pulledBackDatumObjIso (ofHomOver 𝒳 𝒵 k (φ.comp ψ hk)) D i).hom.left ≫
        pullback.fst (D.obj ((φ.comp ψ hk).s₀ i)).hom ((φ.comp ψ hk).h₀ i) =
      (pulledBackDatumObjIso (ofHomOver 𝒳 𝒴 g φ)
            (pulledBackDatum (ofHomOver 𝒴 𝒵 h ψ) D) i).hom.left ≫
        pullback.fst ((pulledBackDatum (ofHomOver 𝒴 𝒵 h ψ) D).obj (φ.s₀ i)).hom (φ.h₀ i) ≫
        (pulledBackDatumObjIso (ofHomOver 𝒴 𝒵 h ψ) D (φ.s₀ i)).hom.left ≫
        pullback.fst (D.obj (ψ.s₀ (φ.s₀ i))).hom (ψ.h₀ (φ.s₀ i)) := by
  simp only [objIso_hom_left_comp]
  exact pullbackCompObjIso_hom_left_fst (D.obj (ψ.s₀ (φ.s₀ i))) (φ.h₀ i) (ψ.h₀ (φ.s₀ i))
    (φ.h₀ i ≫ ψ.h₀ (φ.s₀ i)) rfl

/-- The comparison map on the sources of the gluing isomorphisms of the datum pulled back along
`ψ`, read at the indices coming from `φ`. -/
@[reassoc]
private lemma sourceMapMid_fst (φ : 𝒳.HomOver 𝒴 g) (ψ : 𝒴.HomOver 𝒵 h) (hk : g ≫ h = k)
    (D : DescentData 𝒵.f) (i j : 𝒳.I₀) :
    pulledBackDatumSourceMap (ofHomOver 𝒴 𝒵 h ψ) D (φ.s₀ i) (φ.s₀ j) ≫
        pullback.fst ((D.obj ((φ.comp ψ hk).s₀ i)).hom ≫ 𝒵.f ((φ.comp ψ hk).s₀ i))
          (𝒵.f ((φ.comp ψ hk).s₀ j)) =
      pullback.fst
          (((pulledBackDatum (ofHomOver 𝒴 𝒵 h ψ) D).obj (φ.s₀ i)).hom ≫ 𝒴.f (φ.s₀ i))
          (𝒴.f (φ.s₀ j)) ≫
        (pulledBackDatumObjIso (ofHomOver 𝒴 𝒵 h ψ) D (φ.s₀ i)).hom.left ≫
        pullback.fst (D.obj (ψ.s₀ (φ.s₀ i))).hom (ψ.h₀ (φ.s₀ i)) :=
  pulledBackDatumSourceMap_comp_fst (ofHomOver 𝒴 𝒵 h ψ) D (φ.s₀ i) (φ.s₀ j)

/-- The comparison map on the sources of the gluing isomorphisms of the datum pulled back along
`ψ` projects to the member of the family at the second index. -/
@[reassoc]
private lemma sourceMapMid_snd (φ : 𝒳.HomOver 𝒴 g) (ψ : 𝒴.HomOver 𝒵 h) (hk : g ≫ h = k)
    (D : DescentData 𝒵.f) (i j : 𝒳.I₀) :
    pulledBackDatumSourceMap (ofHomOver 𝒴 𝒵 h ψ) D (φ.s₀ i) (φ.s₀ j) ≫
        pullback.snd ((D.obj ((φ.comp ψ hk).s₀ i)).hom ≫ 𝒵.f ((φ.comp ψ hk).s₀ i))
          (𝒵.f ((φ.comp ψ hk).s₀ j)) =
      pullback.snd
          (((pulledBackDatum (ofHomOver 𝒴 𝒵 h ψ) D).obj (φ.s₀ i)).hom ≫ 𝒴.f (φ.s₀ i))
          (𝒴.f (φ.s₀ j)) ≫ ψ.h₀ (φ.s₀ j) :=
  pulledBackDatumSourceMap_comp_snd (ofHomOver 𝒴 𝒵 h ψ) D (φ.s₀ i) (φ.s₀ j)

/-- **The comparison maps on the sources of the gluing isomorphisms are compatible with the
identification of the components.** -/
lemma srcGluingMap_comp_pulledBackDatumSourceMap (φ : 𝒳.HomOver 𝒴 g) (ψ : 𝒴.HomOver 𝒵 h)
    (hk : g ≫ h = k) (D : DescentData 𝒵.f) (i j : 𝒳.I₀) :
    DescentData.srcGluingMap
          (fun i ↦ (pulledBackDatumCompObjIso φ ψ hk D i).hom) i j ≫
        pulledBackDatumSourceMap (ofHomOver 𝒳 𝒵 k (φ.comp ψ hk)) D i j =
      pulledBackDatumSourceMap (ofHomOver 𝒳 𝒴 g φ)
          (pulledBackDatum (ofHomOver 𝒴 𝒵 h ψ) D) i j ≫
        pulledBackDatumSourceMap (ofHomOver 𝒴 𝒵 h ψ) D (φ.s₀ i) (φ.s₀ j) := by
  refine pullback.hom_ext
    (f := (D.obj ((φ.comp ψ hk).s₀ i)).hom ≫ 𝒵.f ((φ.comp ψ hk).s₀ i))
    (g := 𝒵.f ((φ.comp ψ hk).s₀ j)) ?_ ?_
  · simp only [Category.assoc]
    rw [pulledBackDatumSourceMap_comp_fst (ofHomOver 𝒳 𝒵 k (φ.comp ψ hk)) D i j,
      DescentData.srcGluingMap_fst_assoc, compObjIso_fst, sourceMapMid_fst φ ψ hk D i j,
      pulledBackDatumSourceMap_comp_fst_assoc (ofHomOver 𝒳 𝒴 g φ)
        (pulledBackDatum (ofHomOver 𝒴 𝒵 h ψ) D) i j]
  · simp only [Category.assoc]
    rw [pulledBackDatumSourceMap_comp_snd (ofHomOver 𝒳 𝒵 k (φ.comp ψ hk)) D i j,
      DescentData.srcGluingMap_snd_assoc, sourceMapMid_snd φ ψ hk D i j,
      pulledBackDatumSourceMap_comp_snd_assoc (ofHomOver 𝒳 𝒴 g φ)
        (pulledBackDatum (ofHomOver 𝒴 𝒵 h ψ) D) i j]
    rfl

/-- The identification of the components is compatible with the gluing isomorphisms. -/
lemma pulledBackDatumCompObjIso_gluing (φ : 𝒳.HomOver 𝒴 g) (ψ : 𝒴.HomOver 𝒵 h)
    (hk : g ≫ h = k) (D : DescentData 𝒵.f) (i j : 𝒳.I₀) :
    DescentData.srcGluingMap
          (fun i ↦ (pulledBackDatumCompObjIso φ ψ hk D i).hom) i j ≫
        ((pulledBackDatum (ofHomOver 𝒳 𝒵 k (φ.comp ψ hk)) D).gluingPullbackIso i j).hom =
      ((pulledBackDatum (ofHomOver 𝒳 𝒴 g φ)
            (pulledBackDatum (ofHomOver 𝒴 𝒵 h ψ) D)).gluingPullbackIso i j).hom ≫
        DescentData.tgtGluingMap
          (fun i ↦ (pulledBackDatumCompObjIso φ ψ hk D i).hom) i j := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [DescentData.gluingPullbackIso_hom_fst', DescentData.tgtGluingMap_fst,
      DescentData.srcGluingMap_fst_assoc, DescentData.gluingPullbackIso_hom_fst', Over.w]
  · refine hom_ext_objIso (ofHomOver 𝒳 𝒵 k (φ.comp ψ hk)) D j ?_ ?_
    · simp only [Category.assoc]
      rw [gluing_snd_fst (ofHomOver 𝒳 𝒵 k (φ.comp ψ hk)) D i j,
        DescentData.tgtGluingMap_snd_assoc, compObjIso_fst,
        gluing_snd_fst_assoc (ofHomOver 𝒳 𝒴 g φ)
          (pulledBackDatum (ofHomOver 𝒴 𝒵 h ψ) D) i j,
        gluing_snd_fst (ofHomOver 𝒴 𝒵 h ψ) D (φ.s₀ i) (φ.s₀ j),
        ← Category.assoc, srcGluingMap_comp_pulledBackDatumSourceMap φ ψ hk D i j]
      simp only [Category.assoc]
      rfl
    · simp only [Category.assoc]
      rw [DescentData.tgtGluingMap_snd_assoc,
        Over.w (pulledBackDatumCompObjIso φ ψ hk D j).hom,
        DescentData.gluingPullbackIso_hom_snd, DescentData.gluingPullbackIso_hom_snd,
        DescentData.srcGluingMap_snd]

/-- **Pulling a descent datum back along two morphisms of families in succession is pulling it
back along their composite.** Let `φ : 𝒳 ⟶ 𝒴` and `ψ : 𝒴 ⟶ 𝒵` be morphisms of families of
schemes with fixed target, over `g : R ⟶ T` and `h : T ⟶ W`, and let `k = g ≫ h`. For a descent
datum `D` relative to `𝒵`, the datum obtained by pulling `D` back along `ψ` and then along `φ`
is canonically isomorphic to the datum obtained by pulling it back along `φ ≫ ψ`. -/
def pulledBackDatumCompIso (φ : 𝒳.HomOver 𝒴 g) (ψ : 𝒴.HomOver 𝒵 h) (hk : g ≫ h = k)
    (D : DescentData 𝒵.f) :
    pulledBackDatum (ofHomOver 𝒳 𝒴 g φ) (pulledBackDatum (ofHomOver 𝒴 𝒵 h ψ) D) ≅
      pulledBackDatum (ofHomOver 𝒳 𝒵 k (φ.comp ψ hk)) D :=
  DescentData.isoOfComponents (pulledBackDatumCompObjIso φ ψ hk D)
    (pulledBackDatumCompObjIso_gluing φ ψ hk D)

end MorphismOfSchemeFamilies

end AlgebraicGeometry

end

end
