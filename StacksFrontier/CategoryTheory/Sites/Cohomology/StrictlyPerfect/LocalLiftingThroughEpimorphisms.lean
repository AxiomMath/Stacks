module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# Local lifting of maps out of finite free summands through an epimorphism

Let `(C, O)` be a ringed site and `U` an object of `C`. If `p : G ⟶ F` is an epimorphism of
`O|_U`-modules and `e : E ⟶ F` is any map whose source `E` is a direct summand of a finite
free `O|_U`-module, then `e` lifts through `p` after restricting along the arrows of some
covering sieve of `U`. This is the local lifting step used throughout the theory of strictly
perfect complexes.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coveringSieve_lift`: the local lifting statement,
  Stacks 08FN.
* `AlgebraicGeometry.RingedSite.overFunctor_preservesFiniteCoproduct`: restriction of sheaves
  of modules to a slice preserves finite coproducts.

## Implementation notes

The covering is produced as a sieve rather than a family of arrows, and the conclusion is
stated for every arrow of that sieve, which is what the applications consume.

Being a direct summand of a finite free module is
`AlgebraicGeometry.RingedSite.IsDirectSummandOfFiniteFree`, the predicate underlying Stacks
08FL; it carries the
universe of the sections of the structure sheaf and the universe of the sections of the
modules as independent parameters, and this file instantiates both at `0`, because the
ringed-site statement it feeds is stated at `RingedSite.{u, t, 0}` and the rest of this proof
indexes the finite free module by `Fin n` rather than by `ULift (Fin n)`. The objects and the
morphisms of the site keep independent
universes `u` and `t`: nothing in the argument relates them, and a statement about a
ringed site at `RingedSite.{u, v, 0}` cannot instantiate one that has collapsed them. The
morphism universe is spelled `t` rather than `v` because `v` is already in use here for the
universe of the abelian groups.

The one hypothesis that cannot be dropped is the existence of a sheafification functor for
abelian-group-valued presheaves on `C/U`. Its *left exactness* is deliberately not assumed:
the library's `Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi` proves exactly
`localLift_isLocallySurjective` below but needs `HasSheafify`, which on a slice of a large
site does not follow from `HasWeakSheafify` for small abelian groups. The three private
lemmas below therefore re-derive local surjectivity from an epimorphism by a cokernel
argument that uses only the weak form. Finite infima of covering sieves are
`Stacks.SheafOfModules.FiniteTypeKernel.iInf_mem`, and preservation of finite limits by
restriction is `Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits`.

## References

* [Stacks Project, Tag 08FN](https://stacks.math.columbia.edu/tag/08FN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w t

namespace AlgebraicGeometry.RingedSite


/-- A section of the target of a map of presheaves of abelian groups which dies in a cokernel
of that map over some object is, over that object, in the image. The cokernel is given as an
arbitrary colimit cofork, since in the application it is the one whose sheafification is known
to vanish. -/
private lemma preimage_of_cokernel_vanishes
    {C : Type u} [Category.{t} C] {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    (φ : P ⟶ Q) (cc : CokernelCofork φ) (hc : IsColimit cc)
    {X : Cᵒᵖ} (y : Q.obj X) (hy : cc.π.app X y = 0) :
    ∃ x : P.obj X, φ.app X x = y := by
  let E := (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj X
  let ccX : CokernelCofork (φ.app X) := cc.map E
  have hcX : IsColimit ccX := CokernelCofork.mapIsColimit cc hc E
  let can : CokernelCofork (φ.app X) := CokernelCofork.ofπ
    (cokernel.π (φ.app X)) (CokernelCofork.condition _)
  have hcan : IsColimit can := cokernelIsCokernel (φ.app X)
  let e := hcX.coconePointUniqueUpToIso hcan
  have he : ccX.π ≫ e.hom = can.π := by
    simpa [e, ccX, can] using
      (hcX.comp_coconePointUniqueUpToIso_hom hcan WalkingParallelPair.one)
  have hzero : can.π.hom y = 0 := by
    have hy' : ccX.π.hom y = 0 := by simpa [ccX, E] using hy
    simp [← he, hy']
  have hq : QuotientAddGroup.mk' (AddMonoidHom.range (φ.app X).hom) y = 0 := by
    simpa [can, AddCommGrpCat.cokernelIsoQuotient] using
      congrArg (fun z : can.pt => (AddCommGrpCat.cokernelIsoQuotient (φ.app X)).hom z) hzero
  exact (QuotientAddGroup.eq_zero_iff _).mp hq

/-- A map of presheaves of abelian groups whose sheafification is an epimorphism is locally
surjective. The argument does not assume that sheafification is left exact: the cokernel
presheaf has vanishing sheafification, so each of its sections is locally zero, and a section
of the target which is locally zero in the cokernel is locally in the image. -/
private lemma locallySurjective_of_epi_sheafification
    {C : Type u} [Category.{t} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (φ : P ⟶ Q)
    (hφ : Epi ((presheafToSheaf J AddCommGrpCat.{v}).map φ)) :
    Presheaf.IsLocallySurjective J φ := by
  let F := presheafToSheaf J AddCommGrpCat.{v}
  let cc : CokernelCofork φ := colimit.cocone (parallelPair φ 0)
  have hcc : IsColimit cc := colimit.isColimit (parallelPair φ 0)
  have hmap : IsColimit (cc.map F) := CokernelCofork.mapIsColimit cc hcc F
  have hzero : IsZero ((cc.map F).pt) := CokernelCofork.IsColimit.isZero_of_epi hmap
  have hinj : Presheaf.IsLocallyInjective J (toSheafify J cc.pt) :=
    (J.W_toSheafify cc.pt).isLocallyInjective
  refine ⟨fun {X} y => ?_⟩
  let q := cc.π.app (Opposite.op X) y
  have hq : (toSheafify J cc.pt).app (Opposite.op X) q = 0 := by
    let E := sheafToPresheaf J AddCommGrpCat.{v} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (Opposite.op X)
    let B := E.obj ((cc.map F).pt)
    have hid : 𝟙 B = 0 := (IsZero.iff_id_eq_zero B).mp (Functor.map_isZero E hzero)
    simpa using congrArg (fun f : B ⟶ B => f ((toSheafify J cc.pt).app (Opposite.op X) q)) hid
  apply J.superset_covering ?_ (hinj.equalizerSieve_mem q 0 (by simpa using hq))
  intro Y f hf
  have hvan : cc.π.app (Opposite.op Y) (Q.map f.op y) = 0 := by
    dsimp [Presheaf.equalizerSieve] at hf
    calc
      cc.π.app (Opposite.op Y) (Q.map f.op y) =
          cc.pt.map f.op (cc.π.app (Opposite.op X) y) :=
        NatTrans.naturality_apply cc.π f.op y
      _ = 0 := by simpa [q] using hf
  exact preimage_of_cokernel_vanishes φ cc hcc (Q.map f.op y) hvan

/-- An epimorphism of sheaves of modules is locally surjective on underlying presheaves of
abelian groups. Only the existence of a sheafification functor is assumed, not its left
exactness: the module-sheafification of the cokernel of the underlying map vanishes, and
that already forces local surjectivity. -/
private lemma localLift_isLocallySurjective
    {C : Type u} [Category.{t} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    {M N : SheafOfModules.{v} R} (p : M ⟶ N) [Epi p] :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map p.val) := by
  let L := PresheafOfModules.sheafification (𝟙 R.obj)
  let A := PresheafOfModules.toPresheaf R.obj
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let H := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let p₀ := H.map p
  have hLp : Epi (L.map p₀) := by
    rw [← epi_comp_iff_of_isIso _ (adj.counit.app N)]
    change Epi ((H ⋙ L).map p ≫ adj.counit.app N)
    rw [adj.counit.naturality p]
    infer_instance
  let F := A ⋙ presheafToSheaf J AddCommGrpCat.{v}
  let cc : CokernelCofork p₀ := colimit.cocone (parallelPair p₀ 0)
  have hcc : IsColimit cc := colimit.isColimit (parallelPair p₀ 0)
  have hzF : IsZero ((cc.map F).pt) := Functor.map_isZero (SheafOfModules.toSheaf.{v} R)
    (CokernelCofork.IsColimit.isZero_of_epi (CokernelCofork.mapIsColimit cc hcc L))
  exact locallySurjective_of_epi_sheafification (A.map p₀)
    (Preadditive.epi_of_isZero_cokernel' _ (CokernelCofork.mapIsColimit cc hcc F) hzF)

/-- Restriction of sheaves of modules to a slice of the site preserves finite coproducts.
Restriction preserves all limits, hence finite products; being additive, it therefore
preserves finite biproducts and so finite coproducts. -/
theorem overFunctor_preservesFiniteCoproduct
    {C : Type u} [Category.{t} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (V : C) (n : ℕ) :
    PreservesColimit (Discrete.functor fun _ : Fin n => SheafOfModules.unit R)
      (SheafOfModules.overFunctor.{w} R V) := by
  have : PreservesFiniteLimits (SheafOfModules.overFunctor.{w} R V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V
  have : PreservesBiproduct (fun _ : Fin n => SheafOfModules.unit R)
      (SheafOfModules.overFunctor.{w} R V) :=
    preservesBiproduct_of_preservesProduct _
  exact preservesCoproduct_of_preservesBiproduct _

/-- If an arrow `f : V ⟶ U` lies in the sieve on `U` corresponding to a sieve `S` on
`Over.mk (𝟙 U)`, then `S` contains the arrow `Over.mk f ⟶ Over.mk (𝟙 U)` induced by `f`. -/
theorem overEquiv_homMk_mem {C : Type u} [Category.{t} C] {U V : C}
    (S : Sieve (Over.mk (𝟙 U))) (f : V ⟶ U) (hf : Sieve.overEquiv _ S f) :
    S (Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 U)) := by
  have hh := (Sieve.overEquiv_iff S f).mp hf
  let P : Over U := Over.mk (f ≫ (Over.mk (𝟙 U)).hom)
  have hobj : P = Over.mk f := by
    dsimp [P]
    congr 1
    simp
  let h' : P ⟶ Over.mk (𝟙 U) := Over.homMk f
  have hh' : S h' := by simpa [P] using hh
  have hcomp : eqToHom hobj.symm ≫ h' = Over.homMk f (by simp) := by
    apply Over.OverMorphism.ext
    simp [h', P]
  rw [← hcomp]
  exact S.downward_closed hh' _

/-- A map `q` out of a finite free module lifts through `p : G ⟶ F` after restriction to the
slice over `W`, as soon as each of the global sections of `F` determined by `q` is, over `W`,
the image under `p` of a section of `G`. -/
theorem exists_over_lift_of_free {C : Type u} [Category.{t} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    {R : Sheaf J RingCat.{0}} {F G : SheafOfModules.{0} R} (p : G ⟶ F) {n : ℕ}
    (q : SheafOfModules.free (R := R) (Fin n) ⟶ F) (W : C)
    (a : Fin n → G.val.obj (Opposite.op W))
    (ha : ∀ k, p.val.app (Opposite.op W) (a k) = (F.freeHomEquiv q k).val (Opposite.op W)) :
    ∃ l : (SheafOfModules.free (R := R) (Fin n)).over W ⟶ G.over W,
      l ≫ p.over W = q.over W := by
  let Gf := G.over W
  let pF : Gf ⟶ F.over W := p.over W
  let t : Fin n → Gf.sections := fun k =>
    PresheafOfModules.sectionsMk (fun Y => G.val.map Y.unop.hom.op (a k)) (by
      intro Y Z g
      change G.val.map g.unop.left.op (G.val.map Y.unop.hom.op (a k)) =
        G.val.map Z.unop.hom.op (a k)
      rw [← G.val.map_comp_apply, ← op_comp, Over.w g.unop])
  let H := SheafOfModules.overFunctor R W
  have : PreservesColimit (Discrete.functor fun _ : Fin n => SheafOfModules.unit R) H :=
    overFunctor_preservesFiniteCoproduct W n
  let c := H.mapCocone (SheafOfModules.freeCofan (R := R) (Fin n))
  have hc : IsColimit c :=
    isColimitOfPreserves H (SheafOfModules.isColimitFreeCofan (R := R) (Fin n))
  let η : SheafOfModules.unit (R.over W) ≅ H.obj (SheafOfModules.unit R) := Iso.refl _
  let d : Cofan (fun _ : Fin n => H.obj (SheafOfModules.unit R)) :=
    Cofan.mk Gf (fun i => η.inv ≫ Gf.unitHomEquiv.symm (t i))
  let k : (SheafOfModules.free (R := R) (Fin n)).over W ⟶ Gf := hc.desc d
  refine ⟨k, hc.hom_ext fun i => ?_⟩
  change c.ι.app i ≫ k ≫ pF = c.ι.app i ≫ q.over W
  apply (cancel_epi η.hom).1
  have hsections : SheafOfModules.sectionsMap pF (t i.as) =
      (F.over W).unitHomEquiv (η.hom ≫ c.ι.app i ≫ q.over W) := by
    apply PresheafOfModules.sections_ext
    intro Y
    change p.val.app (Opposite.op Y.unop.left) (G.val.map Y.unop.hom.op (a i.as)) = _
    rw [PresheafOfModules.naturality_apply, ha i.as]
    refine ((F.freeHomEquiv q i.as).property Y.unop.hom.op).trans ?_
    simp [SheafOfModules.freeHomEquiv, η, c, H,
      SheafOfModules.freeCofan, SheafOfModules.ιFree,
      SheafOfModules.overFunctor, SheafOfModules.pushforward,
      Functor.mapCocone_ι_app]
    rfl
  calc
    η.hom ≫ c.ι.app i ≫ k ≫ pF =
        (F.over W).unitHomEquiv.symm (SheafOfModules.sectionsMap pF (t i.as)) := by
      calc
        η.hom ≫ c.ι.app i ≫ k ≫ pF = η.hom ≫ d.ι.app i ≫ pF :=
          congrArg (fun m => η.hom ≫ m ≫ pF) (hc.fac d i)
        _ = η.hom ≫ (η.inv ≫ Gf.unitHomEquiv.symm (t i.as)) ≫ pF := rfl
        _ = (F.over W).unitHomEquiv.symm (SheafOfModules.sectionsMap pF (t i.as)) := by
          dsimp only [Gf]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
          exact SheafOfModules.unitHomEquiv_symm_comp (t i.as) pF
    _ = (F.over W).unitHomEquiv.symm
        ((F.over W).unitHomEquiv (η.hom ≫ c.ι.app i ≫ q.over W)) := congrArg _ hsections
    _ = η.hom ≫ c.ι.app i ≫ q.over W := (F.over W).unitHomEquiv.symm_apply_apply _

/-- **Stacks 08FN.** Let `(C, O)` be a ringed site, `U` an object of `C`, and let
`p : G ⟶ F` be an epimorphism of `O|_U`-modules. A map `e : E ⟶ F` whose source is a direct
summand of a finite free `O|_U`-module lifts through `p` locally on `U`: there is a covering
sieve `S` of `U` such that for every `f : V ⟶ U` in `S` the restriction of `e` to `C/V`
factors through the restriction of `p`.

The lift is produced one coordinate at a time. Writing `E` as a retract of `O|_U^{⊕n}` by
`j : E ⟶ O|_U^{⊕n}` and `r : O|_U^{⊕n} ⟶ E` with `j ≫ r = 𝟙`, the composite `q = r ≫ e` is
determined by `n` global sections of `F` over `U`. Each of them lifts through `p` on a
covering sieve, since `p` is locally surjective; the intersection of those `n` sieves is still
covering, and over it the chosen lifts assemble, by the universal property of the free module,
into a map `O|_U^{⊕n}|_V ⟶ G|_V` over `p`. Precomposing with `j|_V` gives the lift of `e`. -/
@[stacks 08FN]
theorem exists_coveringSieve_lift (X : RingedSite.{u, t, 0}) (U : X.C)
    [HasWeakSheafify (X.J.over U) AddCommGrpCat.{0}]
    [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (E F G : SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (e : E ⟶ F) (p : G ⟶ F) [Epi p]
    (hE : IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E) :
    ∃ S : Sieve U, (S ∈ X.J U) ∧
      (∀ {V : X.C} (f : V ⟶ U), S f →
        ∃ l : E.over (Over.mk f) ⟶ G.over (Over.mk f),
          l ≫ p.over (Over.mk f) = e.over (Over.mk f)) := by
  classical
  let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U
  obtain ⟨n, j₀, r₀, hjr₀⟩ :=
    (isDirectSummandOfFiniteFree_iff_free R E).mp hE
  -- `IsDirectSummandOfFiniteFree` indexes the finite free module by `ULift.{w} (Fin n)`,
  -- since `SheafOfModules.free` indexes by a type in the universe of the sections of the
  -- structure sheaf. Here that universe is `0`, so the index may be transported back to
  -- `Fin n` along `Equiv.ulift`, which is the indexing the rest of this proof uses.
  have eU : SheafOfModules.free (R := R) (ULift.{0} (Fin n))
      ≅ SheafOfModules.free (R := R) (Fin n) :=
    (SheafOfModules.freeFunctor (R := R)).mapIso Equiv.ulift.toIso
  obtain ⟨j, r, hjr⟩ :
      ∃ (j : E ⟶ SheafOfModules.free (R := R) (Fin n))
        (r : SheafOfModules.free (R := R) (Fin n) ⟶ E), j ≫ r = 𝟙 E := by
    refine ⟨j₀ ≫ eU.hom, eU.inv ≫ r₀, ?_⟩
    rw [Category.assoc, ← Category.assoc eU.hom, eU.hom_inv_id, Category.id_comp, hjr₀]
  let J := X.J.over U
  let T : Over U := Over.mk (𝟙 U)
  let q : SheafOfModules.free (R := R) (Fin n) ⟶ F := r ≫ e
  let s : Fin n → F.sections := F.freeHomEquiv q
  let image : Fin n → Sieve T := fun k =>
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map p.val)
      ((s k).val (Opposite.op T))
  let Tcover : Sieve T := ⨅ k : Fin n, image k
  have hTcover : Tcover ∈ J T := Stacks.SheafOfModules.FiniteTypeKernel.iInf_mem J image
    fun k => (localLift_isLocallySurjective R p).imageSieve_mem ((s k).val (Opposite.op T))
  refine ⟨Sieve.overEquiv T Tcover, (X.J.mem_over_iff Tcover).mp hTcover, fun f hf => ?_⟩
  let gT : Over.mk f ⟶ T := Over.homMk f (by simp [T])
  have hfT : Tcover gT := overEquiv_homMk_mem Tcover f hf
  have hmem : ∀ k : Fin n, image k gT := fun k => iInf_le image k gT hfT
  obtain ⟨k, hk⟩ := exists_over_lift_of_free p q (Over.mk f)
    (fun k => Classical.choose (hmem k))
    fun k => (Classical.choose_spec (hmem k)).trans ((s k).property gT.op)
  refine ⟨j.over (Over.mk f) ≫ k, ?_⟩
  rw [Category.assoc, hk]
  change (SheafOfModules.overFunctor R (Over.mk f)).map (j ≫ r ≫ e) =
    (SheafOfModules.overFunctor R (Over.mk f)).map e
  rw [← Category.assoc, hjr, Category.id_comp]


end AlgebraicGeometry.RingedSite

end
