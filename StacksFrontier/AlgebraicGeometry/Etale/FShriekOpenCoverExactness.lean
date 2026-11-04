module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenCoverSignRule
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenCoverStalkCovariance
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenCoverStalkDecomposition

/-!
# Exactness of the Čech complex of an open covering

Let `f : X ⟶ Y` be locally quasi-finite in a big étale site, let `U : I → Opens X` be a family of
open subschemes covering `X` and let `F` be an abelian sheaf on the small étale site of `X`. The
Čech complex

`⋯ ⟶ ⊕_{i₀i₁} f_{i₀i₁,!}(F|_{X_{i₀i₁}}) ⟶ ⊕_{i₀} f_{i₀,!}(F|_{X_{i₀}}) ⟶ f_!F ⟶ 0`

of Stacks 0F5H is acyclic. On the stalk at a geometric point `s` of `Y` the degree-`p` term is the
coproduct of the stalks of `F` over the pairs of a point `x` of the geometric fibre of `f` over `s`
and a `p`-tuple of indices of opens containing `x`, and on those coproducts the differential obeys
the Čech sign rule; the covering hypothesis makes the index types nonempty, so the resulting
simplicial coproduct complex is exact.

## Main results

* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechComplexObj_acyclic` — **Stacks 0F5H,
  exactness**: the Čech complex of an open covering is acyclic.

## Implementation notes

The two inputs of
`AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechComplexObj_acyclic_of_stalkCoefficients` are
produced here: the summand map of a point of the geometric fibre and a tuple of indices is the
inclusion of that point's summand of the stalk of the intersection cut out by the tuple, and its
composite with the covariance map of that intersection is the inclusion of the point's summand of
`(f_!F)_s`, which is Stacks 0F6S part (1) read on the decompositions of Stacks 0F5F.

The stalk of a Čech summand and the stalk of a Čech term are both built from the comparison
isomorphism of Stacks 0F5F, whose source is spelled with the stalk functor of the site and whose
target is spelled with the direct sum over the geometric fibre. The two spellings are
definitionally but not syntactically equal, so the identities relating them are assembled from
`Eq.trans` and `congrArg` rather than by rewriting, and the reassociation steps are factored
through small lemmas about abstract morphisms.

## References

* [Stacks Project, Tag 0F5H](https://stacks.math.columbia.edu/tag/0F5H)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 0F6S](https://stacks.math.columbia.edu/tag/0F6S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped DirectSum

universe u v w t

namespace AlgebraicGeometry.SmallEtale.OpenCoverShriek

section Reassociation

variable {C : Type*} [Category C]

/-- Reassociating a composite in front of a further morphism. -/
private theorem comp_assoc_eq {W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Y} {c : W ⟶ Y}
    (h : a ≫ b = c) (k : Y ⟶ Z) : a ≫ b ≫ k = c ≫ k :=
  (Category.assoc a b k).symm.trans (congrArg (fun z => z ≫ k) h)

/-- Reassociating a composite in front of a further morphism, the value being a composite. -/
private theorem comp_assoc_eq₂ {V W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Y} {c : W ⟶ V} {d : V ⟶ Y}
    (h : a ≫ b = c ≫ d) (k : Y ⟶ Z) : a ≫ b ≫ k = c ≫ d ≫ k :=
  (Category.assoc a b k).symm.trans
    ((congrArg (fun z => z ≫ k) h).trans (Category.assoc c d k))

/-- Reassociating a composite in front of a further morphism, the value being a fourfold
composite. -/
private theorem comp_assoc_eq₄ {V₁ V₂ V₃ W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Y} {c₁ : W ⟶ V₁}
    {c₂ : V₁ ⟶ V₂} {c₃ : V₂ ⟶ V₃} {c₄ : V₃ ⟶ Y}
    (h : a ≫ b = c₁ ≫ c₂ ≫ c₃ ≫ c₄) (k : Y ⟶ Z) :
    a ≫ b ≫ k = c₁ ≫ c₂ ≫ c₃ ≫ c₄ ≫ k := by
  rw [← Category.assoc, h]
  simp only [Category.assoc]

/-- Reassociating a threefold composite in front of a further morphism. -/
private theorem assoc₃ {W X Y Z T : C} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ T) :
    (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  simp only [Category.assoc]

/-- Rewriting the tail of a composite. -/
private theorem comp_congr {V W Z : C} (p : V ⟶ W) {g h : W ⟶ Z} (e : g = h) : p ≫ g = p ≫ h :=
  congrArg (fun z => p ≫ z) e

end Reassociation

section Coproducts

/-- A functor preserving a coproduct carries the inclusion of a factor to the inclusion of the
corresponding factor of the coproduct of the images. -/
private theorem map_ι_comp_preservesCoproductIso_hom {C : Type*} [Category C] {D : Type*}
    [Category D] {J : Type*} (G : C ⥤ D) (g : J → C) [HasCoproduct g]
    [HasCoproduct fun j => G.obj (g j)] [PreservesColimit (Discrete.functor g) G] (i : J) :
    G.map (Sigma.ι g i) ≫ (PreservesCoproduct.iso G g).hom =
      Sigma.ι (fun j => G.obj (g j)) i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitOfHasCoproductOfPreservesColimit G g) (colimit.isColimit _) ⟨i⟩

/-- The identification of a direct sum of abelian groups with its coproduct carries the inclusion
of a factor of the coproduct back to the inclusion of the summand. -/
private theorem ι_comp_directSumCoproductIso_inv {ι : Type w}
    (A : ι → AddCommGrpCat.{max w t}) [inst : DecidableEq ι] (i : ι) :
    Sigma.ι A i ≫ (AddCommGrpCat.directSumCoproductIso A).inv =
      AddCommGrpCat.ofHom (DirectSum.of (fun i => (A i : Type _)) i) := by
  obtain rfl : inst = Classical.decEq ι := Subsingleton.elim _ _
  exact (Iso.comp_inv_eq _).2 (AddCommGrpCat.inj_directSumCoproductIso_hom A i).symm

/-- Transporting the inclusion of a factor of a coproduct along an equality of indices. -/
private theorem eqToHom_comp_ι {J : Type*} {C : Type*} [Category C] (Q : J → C) [HasCoproduct Q]
    {p p' : J} (hp : p = p') :
    eqToHom (congrArg Q hp) ≫ Sigma.ι Q p' = Sigma.ι Q p := by
  cases hp
  exact Category.id_comp _

/-- The inverse of a composite of three isomorphisms carries a morphism `ι` to the composite of
`g` with the inverses of the first two, if `g` followed by the last isomorphism is `ι`. -/
private theorem comp_trans_trans_inv_eq {C : Type*} [Category C] {M P Q R T : C} (S : P ≅ Q)
    (D : Q ≅ R) (W : R ≅ T) {g : M ⟶ R} {ι : M ⟶ T} (h : g ≫ W.hom = ι) :
    ι ≫ (S ≪≫ D ≪≫ W).inv = g ≫ D.inv ≫ S.inv := by
  simp [← h]

end Coproducts

section Summand

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  {I : Type (max (u + 1) v)} (U : I → (B.inclusion.obj X).Opens)
  (s : GeometricPoint Y.obj)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The stalks of the restriction of `F` to an intersection of the covering, over the geometric
fibre of that intersection. -/
private abbrev cechSummandFamily {n : ℕ} (t : Fin n → I) :
    GeometricFiberPoint B (openSchemeι B (coverOpen B U t) ≫ f) s →
      AddCommGrpCat.{max (u + 1) v} :=
  fun y => etaleStalk B (openScheme B (coverOpen B U t)).obj
    (openScheme B (coverOpen B U t)).property
    (y.toGeometricPoint B (openSchemeι B (coverOpen B U t) ≫ f) s)
    ((openRestriction.{u, v} B (openSchemeι B (coverOpen B U t))).obj F).obj

/-- The stalks of `F` over the geometric fibre of an intersection of the covering, indexed by the
points of that fibre. -/
private abbrev cechSummandStalkFamily {n : ℕ} (t : Fin n → I) :
    GeometricFiberPoint B (openSchemeι B (coverOpen B U t) ≫ f) s →
      AddCommGrpCat.{max (u + 1) v} :=
  fun y => fiberPointStalk.{u, v} B f s F
    (openFiberPoint B (openSchemeι B (coverOpen B U t)) f s y)

/-- The stalks of `F` over the pairs of a point of the geometric fibre and a tuple of indices of
opens containing it. -/
private abbrev cechStalkFamily (n : ℕ) :
    (Σ x : GeometricFiberPoint B f s, Fin n → fiberPointCoverIndex.{u, v} B f U s x) →
      AddCommGrpCat.{max (u + 1) v} :=
  fun q => fiberPointStalk.{u, v} B f s F q.1

/-- The stalks of `F` over the geometric fibre of `f`. -/
private abbrev fiberStalkFamily :
    GeometricFiberPoint B f s → AddCommGrpCat.{max (u + 1) v} :=
  fun x => fiberPointStalk.{u, v} B f s F x

/-- The inclusion of the summand of a point of the geometric fibre of `f` into the stalk of `f_!F`,
on the stalk decomposition of Stacks 0F5F. -/
private def fiberPointStalkι (x : GeometricFiberPoint B f s) :
    fiberPointStalk.{u, v} B f s F x ⟶
      ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).obj ((fShriekFunctor.{u, v} B f).obj F) :=
  Sigma.ι (fiberStalkFamily.{u, v} B f s F) x ≫
    (AddCommGrpCat.directSumCoproductIso.{u, max (u + 1) v}
      (fiberStalkFamily.{u, v} B f s F)).inv ≫
    (fShriekStalkIso.{u, v} B f s F).inv

/-- **Stacks 0F5F, part (1), summandwise.** On the stalk decomposition of a summand of the Čech
complex, the inclusion of the summand of a point of the geometric fibre of the intersection is the
inclusion of the corresponding direct summand. -/
private theorem ι_comp_cechSummandStalkIso_inv {n : ℕ} (t : Fin n → I)
    (y : GeometricFiberPoint B (openSchemeι B (coverOpen B U t) ≫ f) s) :
    Sigma.ι (cechSummandStalkFamily.{u, v} B f U s F t) y ≫
        (cechSummandStalkIso.{u, v} B f U s F t).inv =
      (openFiberStalkIso.{u, v} B (openSchemeι B (coverOpen B U t)) f F s y).inv ≫
        Sigma.ι (cechSummandFamily.{u, v} B f U s F t) y ≫
        (AddCommGrpCat.directSumCoproductIso.{u, max (u + 1) v}
          (cechSummandFamily.{u, v} B f U s F t)).inv ≫
        (fShriekStalkIso.{u, v} B (openSchemeι B (coverOpen B U t) ≫ f) s
          ((openRestriction.{u, v} B (openSchemeι B (coverOpen B U t))).obj F)).inv := by
  have hW : Sigma.ι (cechSummandFamily.{u, v} B f U s F t) y ≫
      (Sigma.whiskerEquiv (Equiv.refl
          (GeometricFiberPoint B (openSchemeι B (coverOpen B U t) ≫ f) s))
        (fun y' => (openFiberStalkIso.{u, v} B (openSchemeι B (coverOpen B U t))
          f F s y').symm)).hom =
      (openFiberStalkIso.{u, v} B (openSchemeι B (coverOpen B U t)) f F s y).hom ≫
        Sigma.ι (cechSummandStalkFamily.{u, v} B f U s F t) y :=
    Sigma.ι_comp_map' _ _ y
  exact (comp_trans_trans_inv_eq _ _ _
      (by rw [Category.assoc, hW, Iso.inv_hom_id_assoc])).trans (Category.assoc _ _ _)

/-- **The degree-zero stalk decomposition of the Čech complex.** The summand of a point of the
geometric fibre, indexed by the empty tuple, is the corresponding summand of `(f_!F)_s`. -/
private theorem ι_comp_cechStalkZeroIso_inv (x : GeometricFiberPoint B f s)
    (q : Fin 0 → fiberPointCoverIndex.{u, v} B f U s x) :
    Sigma.ι (cechStalkFamily.{u, v} B f U s F 0) ⟨x, q⟩ ≫
        (cechStalkZeroIso.{u, v} B f U s F).inv =
      fiberPointStalkι.{u, v} B f s F x := by
  obtain rfl : q = default := Unique.eq_default q
  exact comp_trans_trans_inv_eq _ _ _
    ((Sigma.ι_comp_map' _ _ x).trans (Category.id_comp _))

/-- **The stalk of a Čech summand inclusion in positive degree.** On the stalk decompositions, the
inclusion of the summand of a tuple takes the summand of a point of the geometric fibre of the
corresponding intersection to the summand of that point together with the tuple. -/
private theorem ι_comp_cechStalkSuccIso_hom (n : ℕ) (t : Fin (n + 1) → I)
    (y : GeometricFiberPoint B (openSchemeι B (coverOpen B U t) ≫ f) s) :
    Sigma.ι (cechSummandStalkFamily.{u, v} B f U s F t) y ≫
        (cechSummandStalkIso.{u, v} B f U s F t).inv ≫
        ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
            (A := AddCommGrpCat.{max (u + 1) v})).map
          (cechObjTermι.{u, v} B f U F (n + 1) t) ≫
        (cechStalkSuccIso.{u, v} B f U s F n).hom =
      Sigma.ι (cechStalkFamily.{u, v} B f U s F (n + 1))
        (coverFiberTupleEquiv.{u, v} B f s U (n + 1) ⟨t, y⟩) := by
  have hcol : HasColimitsOfShape (Discrete (Fin (n + 1) → I))
      (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) :=
    Sheaf.instHasColimitsOfShape
  have h1 : ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
        (cechObjTermι.{u, v} B f U F (n + 1) t) ≫
      (((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).mapIso
        (PreservesCoproduct.iso ((evaluation _ _).obj F)
          (cechFamily.{u, v} B f U (n + 1)))).hom =
      ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
        (Sigma.ι (fun t' => (cechFamily.{u, v} B f U (n + 1) t').obj F) t) :=
    (Functor.map_comp _ _ _).symm.trans
      (congrArg ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
        (map_ι_comp_preservesCoproductIso_hom ((evaluation _ _).obj F)
          (cechFamily.{u, v} B f U (n + 1)) t))
  have h2 : ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
        (Sigma.ι (fun t' => (cechFamily.{u, v} B f U (n + 1) t').obj F) t) ≫
      (PreservesCoproduct.iso ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v}))
        (fun t' => (cechFamily.{u, v} B f U (n + 1) t').obj F)).hom =
      Sigma.ι (fun t' => ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).obj
          ((cechFamily.{u, v} B f U (n + 1) t').obj F)) t :=
    map_ι_comp_preservesCoproductIso_hom _ _ t
  have h3 : Sigma.ι (fun t' => ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).obj
            ((cechFamily.{u, v} B f U (n + 1) t').obj F)) t ≫
      (Sigma.whiskerEquiv (Equiv.refl (Fin (n + 1) → I))
        (fun t' => (cechSummandStalkIso.{u, v} B f U s F t').symm)).hom =
      (cechSummandStalkIso.{u, v} B f U s F t).hom ≫
        Sigma.ι (fun t' : Fin (n + 1) → I =>
          ∐ cechSummandStalkFamily.{u, v} B f U s F t') t :=
    Sigma.ι_comp_map' _ _ t
  have h4 : Sigma.ι (fun t' : Fin (n + 1) → I =>
          ∐ cechSummandStalkFamily.{u, v} B f U s F t') t ≫
      (sigmaSigmaIso (fun t' : Fin (n + 1) → I =>
          GeometricFiberPoint B (openSchemeι B (coverOpen B U t') ≫ f) s)
        (fun t' y' => cechSummandStalkFamily.{u, v} B f U s F t' y')).hom =
      Sigma.desc fun y' => Sigma.ι (fun p : Σ t' : Fin (n + 1) → I,
          GeometricFiberPoint B (openSchemeι B (coverOpen B U t') ≫ f) s =>
        cechSummandStalkFamily.{u, v} B f U s F p.1 p.2) ⟨t, y'⟩ :=
    Sigma.ι_desc _ t
  have h5 : Sigma.ι (fun p : Σ t' : Fin (n + 1) → I,
          GeometricFiberPoint B (openSchemeι B (coverOpen B U t') ≫ f) s =>
        cechSummandStalkFamily.{u, v} B f U s F p.1 p.2) ⟨t, y⟩ ≫
      (Sigma.whiskerEquiv
        (f := fun p : Σ t' : Fin (n + 1) → I,
            GeometricFiberPoint B (openSchemeι B (coverOpen B U t') ≫ f) s =>
          cechSummandStalkFamily.{u, v} B f U s F p.1 p.2)
        (g := cechStalkFamily.{u, v} B f U s F (n + 1))
        (coverFiberTupleEquiv.{u, v} B f s U (n + 1)) (fun _ => Iso.refl _)).hom =
      Sigma.ι (cechStalkFamily.{u, v} B f U s F (n + 1))
        (coverFiberTupleEquiv.{u, v} B f s U (n + 1) ⟨t, y⟩) :=
    (Sigma.ι_comp_map' _ _ _).trans (Category.id_comp _)
  have hchain : Sigma.ι (cechSummandStalkFamily.{u, v} B f U s F t) y ≫
      (cechSummandStalkIso.{u, v} B f U s F t).inv ≫
      ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
        (cechObjTermι.{u, v} B f U F (n + 1) t) ≫
      ((((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
            (A := AddCommGrpCat.{max (u + 1) v})).mapIso
          (PreservesCoproduct.iso ((evaluation _ _).obj F)
            (cechFamily.{u, v} B f U (n + 1)))).hom ≫
        (PreservesCoproduct.iso ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
            (A := AddCommGrpCat.{max (u + 1) v}))
          (fun t' => (cechFamily.{u, v} B f U (n + 1) t').obj F)).hom ≫
        (Sigma.whiskerEquiv (Equiv.refl (Fin (n + 1) → I))
          (fun t' => (cechSummandStalkIso.{u, v} B f U s F t').symm)).hom ≫
        (sigmaSigmaIso (fun t' : Fin (n + 1) → I =>
            GeometricFiberPoint B (openSchemeι B (coverOpen B U t') ≫ f) s)
          (fun t' y' => cechSummandStalkFamily.{u, v} B f U s F t' y')).hom ≫
        (Sigma.whiskerEquiv
          (f := fun p : Σ t' : Fin (n + 1) → I,
              GeometricFiberPoint B (openSchemeι B (coverOpen B U t') ≫ f) s =>
            cechSummandStalkFamily.{u, v} B f U s F p.1 p.2)
          (g := cechStalkFamily.{u, v} B f U s F (n + 1))
          (coverFiberTupleEquiv.{u, v} B f s U (n + 1)) (fun _ => Iso.refl _)).hom) =
      Sigma.ι (cechStalkFamily.{u, v} B f U s F (n + 1))
        (coverFiberTupleEquiv.{u, v} B f s U (n + 1) ⟨t, y⟩) := by
    rw [comp_assoc_eq h1, comp_assoc_eq h2, comp_assoc_eq₂ h3, Iso.inv_hom_id_assoc,
      comp_assoc_eq h4, ← Category.assoc, Sigma.ι_desc, h5]
  exact hchain

/-- **Stacks 0F6S, part (1), on the Čech stalk decompositions.** The covariance map of an
intersection carries the summand of a point of the geometric fibre of that intersection to the
summand of its image in the geometric fibre of `f`. -/
private theorem ι_comp_cechSummandStalkIso_inv_comp_covariance {n : ℕ} (t : Fin n → I)
    (y : GeometricFiberPoint B (openSchemeι B (coverOpen B U t) ≫ f) s) :
    Sigma.ι (cechSummandStalkFamily.{u, v} B f U s F t) y ≫
        (cechSummandStalkIso.{u, v} B f U s F t).inv ≫
        ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
            (A := AddCommGrpCat.{max (u + 1) v})).map
          ((openCovarianceShriekMap.{u, v} B (openSchemeι B (coverOpen B U t)) f).app F) =
      fiberPointStalkι.{u, v} B f s F
        (openFiberPoint B (openSchemeι B (coverOpen B U t)) f s y) := by
  classical
  have hbr := ofHom_of_comp_fShriekStalkIso_openCovariance.{u, v} B
    (openSchemeι B (coverOpen B U t)) f F s y
  have hbr' := ((Iso.eq_comp_inv (fShriekStalkIso.{u, v} B f s F)).2
    ((assoc₃ _ _ _ _).trans hbr)).trans (Category.assoc _ _ _)
  exact (comp_assoc_eq₄ (ι_comp_cechSummandStalkIso_inv.{u, v} B f U s F t y)
      (((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map
          ((openCovarianceShriekMap.{u, v} B (openSchemeι B (coverOpen B U t)) f).app F))).trans
    ((comp_congr _ (comp_assoc_eq (ι_comp_directSumCoproductIso_inv
          (cechSummandFamily.{u, v} B f U s F t) y) _)).trans
      ((comp_congr _ hbr').trans
        ((Iso.inv_hom_id_assoc _ _).trans
          ((congrArg (fun z => z ≫ (fShriekStalkIso.{u, v} B f s F).inv)
              (ι_comp_directSumCoproductIso_inv
                (fiberStalkFamily.{u, v} B f s F) _).symm).trans
            (Category.assoc _ _ _)))))

/-- The summand of a point of the geometric fibre of `f` together with a tuple of indices of opens
containing it, read in the stalk of the Čech summand of that tuple. -/
private def cechStalkCoeff (n : ℕ) (x : GeometricFiberPoint B f s)
    (q : Fin n → fiberPointCoverIndex.{u, v} B f U s x) :
    fiberPointStalk.{u, v} B f s F x ⟶
      ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).obj
        ((openShriekPushforward.{u, v} B
          (openSchemeι B (coverOpen B U fun k => (q k).1)) f).obj F) :=
  eqToHom (congrArg (fiberPointStalk.{u, v} B f s F)
      (openFiberPoint_coverFiberLift.{u, v} B f U s x q).symm) ≫
    Sigma.ι (cechSummandStalkFamily.{u, v} B f U s F fun k => (q k).1)
      (coverFiberLift.{u, v} B f U s x q) ≫
    (cechSummandStalkIso.{u, v} B f U s F fun k => (q k).1).inv

/-- **Stacks 0F6S, part (1), summandwise.** The composite of the summand map of a tuple with the
covariance map of the intersection it cuts out depends only on the point of the geometric fibre. -/
private theorem cechStalkCoeff_comp_covariance (n : ℕ) (x : GeometricFiberPoint B f s)
    (q : Fin n → fiberPointCoverIndex.{u, v} B f U s x) :
    cechStalkCoeff.{u, v} B f U s F n x q ≫
        ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
            (A := AddCommGrpCat.{max (u + 1) v})).map
          ((openCovarianceShriekMap.{u, v} B
            (openSchemeι B (coverOpen B U fun k => (q k).1)) f).app F) =
      fiberPointStalkι.{u, v} B f s F x :=
  (Category.assoc _ _ _).trans
    ((comp_congr _ ((Category.assoc _ _ _).trans
        (ι_comp_cechSummandStalkIso_inv_comp_covariance.{u, v} B f U s F
          (fun k => (q k).1) (coverFiberLift.{u, v} B f U s x q)))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ (AddCommGrpCat.directSumCoproductIso.{u, max (u + 1) v}
              (fiberStalkFamily.{u, v} B f s F)).inv ≫
            (fShriekStalkIso.{u, v} B f s F).inv)
          (eqToHom_comp_ι (fiberStalkFamily.{u, v} B f s F)
            (openFiberPoint_coverFiberLift.{u, v} B f U s x q).symm))))

/-- **The stalk decomposition is summandwise.** The inclusion of the summand of a point of the
geometric fibre and a tuple of indices of opens containing it factors through the summand of the
intersection cut out by the tuple. -/
private theorem ι_comp_cechStalkIso_hom (n : ℕ) (x : GeometricFiberPoint B f s)
    (q : Fin n → fiberPointCoverIndex.{u, v} B f U s x) :
    Sigma.ι (cechStalkFamily.{u, v} B f U s F n) ⟨x, q⟩ ≫
        (cechStalkIso.{u, v} B f U s F n).hom =
      cechStalkCoeff.{u, v} B f U s F n x q ≫
        ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
            (A := AddCommGrpCat.{max (u + 1) v})).map
          (cechObjTermι.{u, v} B f U F n fun k => (q k).1) := by
  cases n with
  | zero =>
    exact (ι_comp_cechStalkZeroIso_inv.{u, v} B f U s F x q).trans
      (cechStalkCoeff_comp_covariance.{u, v} B f U s F 0 x q).symm
  | succ m =>
    have hk : ((eqToHom (congrArg (fiberPointStalk.{u, v} B f s F)
              (openFiberPoint_coverFiberLift.{u, v} B f U s x q).symm) ≫
            Sigma.ι (cechSummandStalkFamily.{u, v} B f U s F fun k => (q k).1)
              (coverFiberLift.{u, v} B f U s x q) ≫
            (cechSummandStalkIso.{u, v} B f U s F fun k => (q k).1).inv) ≫
          ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
              (A := AddCommGrpCat.{max (u + 1) v})).map
            (cechObjTermι.{u, v} B f U F (m + 1) fun k => (q k).1)) ≫
        (cechStalkSuccIso.{u, v} B f U s F m).hom =
        Sigma.ι (cechStalkFamily.{u, v} B f U s F (m + 1)) ⟨x, q⟩ := by
      rw [Category.assoc, Category.assoc, Category.assoc,
        ι_comp_cechStalkSuccIso_hom.{u, v} B f U s F m (fun k => (q k).1)
          (coverFiberLift.{u, v} B f U s x q)]
      exact eqToHom_comp_ι (cechStalkFamily.{u, v} B f U s F (m + 1))
        (coverFiberTupleEquiv_coverFiberLift.{u, v} B f U s x q).symm
    exact (Iso.comp_inv_eq _).2 hk.symm

end Summand

section Exactness

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  {I : Type (max (u + 1) v)} (U : I → (B.inclusion.obj X).Opens)

/-- **Stacks 0F5H, exactness.** For a family of open subschemes covering `X`, the Čech complex
`⋯ ⟶ ⊕_{i₀} f_{i₀,!}(F|_{X_{i₀}}) ⟶ f_!F ⟶ 0` of an abelian sheaf `F` on the small étale site of
`X` is acyclic. -/
@[stacks 0F5H "exactness of the complex"]
public theorem cechComplexObj_acyclic (hU : (⨆ i, U i) = ⊤)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    (cechComplexObj.{u, v} B f U F).Acyclic :=
  cechComplexObj_acyclic_of_stalkCoefficients.{u, v} B f U hU F
    (fun s n => cechStalkIso.{u, v} B f U s F n)
    (fun s x => fiberPointStalkι.{u, v} B f s F x)
    (fun s n x q => cechStalkCoeff.{u, v} B f U s F n x q)
    (fun s n x q => cechStalkCoeff_comp_covariance.{u, v} B f U s F n x q)
    (fun s n x q => ι_comp_cechStalkIso_hom.{u, v} B f U s F n x q)

end Exactness

end AlgebraicGeometry.SmallEtale.OpenCoverShriek

end
