module

public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Etale

/-!
# The germ morphism induced by a morphism of schemes

A morphism of schemes `f : X ⟶ Y` and a point `x` of `X` determine a morphism of germs
`⟨X, x⟩ ⟶ ⟨Y, f x⟩`, represented on the whole of `X` regarded as its own top open subset.
This file constructs that germ morphism, shows that it is compatible with composition, and
shows that it is étale as a morphism of germs as soon as `f` is étale.

## Main definitions

* `AlgebraicGeometry.MorphismOfGerms.ofSchemeHomOfEq` is the germ morphism induced by a
  scheme morphism at a source point, with the target point supplied together with a proof
  that it is the image of the source point.
* `AlgebraicGeometry.MorphismOfGerms.ofSchemeHom` is the special case in which the target
  point is literally the image point.

## Main results

* `AlgebraicGeometry.MorphismOfGerms.ofSchemeHomOfEq_comp` identifies the composite of two
  induced germ morphisms with the one induced by the composite scheme morphism.
* `AlgebraicGeometry.MorphismOfGerms.isEtale_ofSchemeHomOfEq`: an étale morphism of schemes
  induces an étale morphism of germs.

## Implementation notes

The representative is taken on `⊤`, composed with the canonical isomorphism
`AlgebraicGeometry.Scheme.topIso` from the top open subscheme to the ambient scheme, since a
representative is by definition a morphism out of an open subscheme. The target point is kept
as a separate argument rather than being forced to be `f x`, because the composition lemma is
applied in situations where the two are only propositionally equal; `ofSchemeHom` is the
reducible specialisation that most clients want.

The composition lemma is proved by comparing the two representatives on `⊤`: the domain of
the composite representative is the image in `X` of the preimage of the second domain, which
here is all of `X`, and the identification of that domain with `⊤` is what the chain of
`isoOfEq`/`isoImage` rewrites carries out.

## References

* [Stacks Project, Tag 04QR](https://stacks.math.columbia.edu/tag/04QR)
* [Stacks Project, Tag 04R7](https://stacks.math.columbia.edu/tag/04R7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.MorphismOfGerms

/-- The germ morphism induced by a scheme morphism `f` at a point `x` of its source, with the
distinguished target point given by an equality `f x = y`. It is represented on the whole
source scheme. -/
noncomputable def ofSchemeHomOfEq {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (hxy : f x = y) : MorphismOfGerms ⟨X, x⟩ ⟨Y, y⟩ :=
  mk { source := ⊤
       mem_source := by simp
       hom := X.topIso.hom ≫ f
       map_point := by change f x = y; exact hxy }

/-- The germ morphism induced by a scheme morphism at a point of its source. -/
noncomputable abbrev ofSchemeHom {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    MorphismOfGerms ⟨X, x⟩ ⟨Y, f x⟩ :=
  ofSchemeHomOfEq f x (f x) rfl

/-- The composite of the germ morphisms induced by `f` and `g` is the germ morphism induced
by `f ≫ g`. -/
theorem ofSchemeHomOfEq_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) (y : Y) (z : Z) (hxy : f x = y) (hyz : g y = z) :
    comp (ofSchemeHomOfEq f x y hxy) (ofSchemeHomOfEq g y z hyz) =
      ofSchemeHomOfEq (f ≫ g) x z (by
        calc
          (f ≫ g) x = g (f x) := by rw [← Scheme.Hom.comp_apply]
          _ = g y := congrArg g hxy
          _ = z := hyz) := by
  show comp (mk _) (mk _) = _
  rw [comp_mk]
  let fr : Representative ⟨X, x⟩ ⟨Y, y⟩ :=
    { source := ⊤
      mem_source := by simp
      hom := X.topIso.hom ≫ f
      map_point := hxy }
  let gr : Representative ⟨Y, y⟩ ⟨Z, z⟩ :=
    { source := ⊤
      mem_source := by simp
      hom := Y.topIso.hom ≫ g
      map_point := hyz }
  let rr : Representative ⟨X, x⟩ ⟨Z, z⟩ :=
    { source := ⊤
      mem_source := by simp
      hom := X.topIso.hom ≫ (f ≫ g)
      map_point := by
        calc
          (f ≫ g) x = g (f x) := by rw [← Scheme.Hom.comp_apply]
          _ = g y := congrArg g hxy
          _ = z := hyz }
  show mk (compRepresentative fr gr) = mk rr
  let _ : IsOpenImmersion X.topIso.hom := inferInstance
  let hC : (⊤ : X.Opens) = (compRepresentative fr gr).source := by
    simp [compRepresentative, fr, gr]
  have hR : (⊤ : X.Opens) = rr.source := rfl
  apply mk_eq_mk_iff.mpr
  refine ⟨⊤, by simp, hC.le, hR.le, ?_⟩
  show X.homOfLE hC.le ≫ (compRepresentative fr gr).hom =
    X.homOfLE hR.le ≫ rr.hom
  have hpre : fr.hom ⁻¹ᵁ gr.source = ⊤ := by simp [fr, gr]
  have hImage : fr.source.ι ''ᵁ (fr.hom ⁻¹ᵁ gr.source) =
      (compRepresentative fr gr).source := rfl
  have hImageFac := Scheme.isoOfEq_hom_ι X hImage
  have hIsoImageFac := Scheme.Hom.isoImage_hom_ι fr.source.ι (fr.hom ⁻¹ᵁ gr.source)
  have hPreFac := Scheme.isoOfEq_hom_ι fr.source.toScheme hpre.symm
  have hIso : X.homOfLE hC.le =
      fr.source.toScheme.topIso.inv ≫
        (fr.source.toScheme.isoOfEq hpre.symm).hom ≫
        (Scheme.Hom.isoImage fr.source.ι (fr.hom ⁻¹ᵁ gr.source)).hom ≫
        (X.isoOfEq hImage).hom := by
    have hleft : X.homOfLE hC.le ≫ (compRepresentative fr gr).source.ι = fr.source.ι := by
      rw [Scheme.homOfLE_ι]
    have hright :
        (fr.source.toScheme.topIso.inv ≫
          (fr.source.toScheme.isoOfEq hpre.symm).hom ≫
          (Scheme.Hom.isoImage fr.source.ι (fr.hom ⁻¹ᵁ gr.source)).hom ≫
          (X.isoOfEq hImage).hom) ≫ (compRepresentative fr gr).source.ι = fr.source.ι := by
      calc
        _ = fr.source.toScheme.topIso.inv ≫
            ((fr.source.toScheme.isoOfEq hpre.symm).hom ≫
              ((Scheme.Hom.isoImage fr.source.ι (fr.hom ⁻¹ᵁ gr.source)).hom ≫
                ((X.isoOfEq hImage).hom ≫
                  (compRepresentative fr gr).source.ι))) := by
              simp only [Category.assoc]
        _ = fr.source.toScheme.topIso.inv ≫
            ((fr.source.toScheme.isoOfEq hpre.symm).hom ≫
              ((Scheme.Hom.isoImage fr.source.ι (fr.hom ⁻¹ᵁ gr.source)).hom ≫
                (fr.source.ι ''ᵁ (fr.hom ⁻¹ᵁ gr.source)).ι)) :=
              congrArg (fun k =>
                fr.source.toScheme.topIso.inv ≫
                  ((fr.source.toScheme.isoOfEq hpre.symm).hom ≫
                    ((Scheme.Hom.isoImage fr.source.ι (fr.hom ⁻¹ᵁ gr.source)).hom ≫ k)))
                hImageFac
        _ = fr.source.toScheme.topIso.inv ≫
            ((fr.source.toScheme.isoOfEq hpre.symm).hom ≫
              ((fr.hom ⁻¹ᵁ gr.source).ι ≫ fr.source.ι)) :=
              congrArg (fun k => fr.source.toScheme.topIso.inv ≫
                ((fr.source.toScheme.isoOfEq hpre.symm).hom ≫ k)) hIsoImageFac
        _ = fr.source.toScheme.topIso.inv ≫
            ((⊤ : fr.source.toScheme.Opens).ι ≫ fr.source.ι) :=
              congrArg (fun k => fr.source.toScheme.topIso.inv ≫
                (k ≫ fr.source.ι)) hPreFac
        _ = fr.source.ι := by simp
    exact (cancel_mono (compRepresentative fr gr).source.ι).mp (hleft.trans hright.symm)
  rw [hIso]
  dsimp only [compRepresentative] at ⊢
  have hfrhom : fr.hom = X.topIso.hom ≫ f := rfl
  have hgrhom : gr.hom = Y.topIso.hom ≫ g := rfl
  apply (cancel_epi X.topIso.inv).1
  have hgrhom' : gr.hom = gr.source.ι ≫ g := by
    rw [hgrhom]
    rfl
  have hRestrict :
      fr.hom ∣_ gr.source ≫ gr.hom = (fr.hom ⁻¹ᵁ gr.source).ι ≫ fr.hom ≫ g := by
    rw [hgrhom']
    exact morphismRestrict_ι_assoc fr.hom gr.source g
  rw [hRestrict]
  dsimp only [rr] at ⊢
  simp only [Category.assoc, Category.id_comp, Scheme.isoOfEq_rfl, Iso.refl_hom]
  rw [Iso.hom_inv_id_assoc]
  simp only [← Category.assoc, hPreFac]
  have hfrTop : fr.source.toScheme.topIso.inv ≫ (⊤ : fr.source.toScheme.Opens).ι =
      𝟙 fr.source.toScheme :=
    Scheme.toIso_inv_ι _
  rw [Category.assoc X.topIso.inv fr.source.toScheme.topIso.inv
    (⊤ : fr.source.toScheme.Opens).ι]
  rw [hfrTop]
  rw [hfrhom]
  dsimp [fr] at ⊢
  simp [Scheme.toIso_inv_ι]

/-- An étale morphism of schemes induces an étale morphism of germs. -/
theorem isEtale_ofSchemeHomOfEq {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (hxy : f x = y) (hf : Etale f) : IsEtale (ofSchemeHomOfEq f x y hxy) := by
  let _ : Etale X.topIso.hom := inferInstance
  have hcomp : Etale (X.topIso.hom ≫ f) := Etale.etale_comp _ _
  refine ⟨{ source := ⊤
            mem_source := by simp
            hom := X.topIso.hom ≫ f
            map_point := by change f x = y; exact hxy }, ?_, hcomp⟩
  rfl

end AlgebraicGeometry.MorphismOfGerms

end
