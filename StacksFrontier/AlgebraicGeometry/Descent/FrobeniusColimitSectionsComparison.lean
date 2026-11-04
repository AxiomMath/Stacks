module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFunctorial
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitRingSections
public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.FrobeniusColimitGlobalSections

/-!
# The comparison of `colim_F Γ(X, 𝒪)` with `Γ(colim_F 𝒪_X, X)`

Let `p` be a prime and let `X` be a scheme in characteristic `p`. There are two Frobenius
colimits of the global functions of `X`: the colimit

`colim_F Γ(X, 𝒪) = colim (Γ(X, 𝒪) →^F Γ(X, 𝒪) →^F ⋯)`

of the global sections themselves, which is a presheaf of sets on the category of all schemes
(`AlgebraicGeometry.frobeniusColimitGlobalSections`), and the global sections

`Γ(colim_F 𝒪_X, X)`

of the sheaf of rings `colim_F 𝒪_X` of Stacks Tag 0EXB, out of which the Hom-sets of
`AlgebraicGeometry.frobeniusColimitVectorBundles` are built. This file builds the canonical map
from the first to the second, shows that it is natural in `X` and that it is **bijective when `X`
is quasi-compact and quasi-separated**.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitSectionsLeg` and
  `AlgebraicGeometry.frobeniusColimitSectionsCocone`: the cocone on the Frobenius tower of
  `Γ(X, 𝒪)` whose stage-`n` leg is the stage-`n` coprojection of `colim_F 𝒪_X` on global
  sections.
* `AlgebraicGeometry.frobeniusColimitSectionsComparison`: **the comparison
  `colim_F Γ(X, 𝒪) ⟶ Γ(colim_F 𝒪_X, X)`.**
* `AlgebraicGeometry.frobeniusColimitSectionsRestrict`: the canonical morphism
  `colim_F 𝒪_Y ⟶ f_*(colim_F 𝒪_X)` of
  `AlgebraicGeometry.frobeniusColimitStructureSheafHom`, read on global sections.

## Main results

* `AlgebraicGeometry.frobeniusColimitSectionsComparison_stage`: the comparison takes the class of
  a global function at stage `n` of the Frobenius tower to its image under the stage-`n`
  coprojection. This determines it.
* `AlgebraicGeometry.frobeniusColimitSectionsRestrict_stage`: restriction along `f` takes the
  image of a global function under the stage-`n` coprojection on `Y` to the image of its
  restriction under the stage-`n` coprojection on `X`.
* `AlgebraicGeometry.frobeniusColimitSectionsComparison_naturality`: **the comparison is natural
  in `X`.**
* `AlgebraicGeometry.bijective_toFrobeniusColimitRingSheaf_app`: **no sheafification is needed
  over a quasi-compact open** — `(colim_F 𝒪_X)(U) = colim_j 𝒪_X(U)` there. This is the
  comparison of Stacks Tag 0EXD over an arbitrary quasi-compact open, the comparison itself
  being the sheafification map `AlgebraicGeometry.toFrobeniusColimitRingSheaf`.
* `AlgebraicGeometry.surjective_frobeniusColimitSectionsComparison`,
  `AlgebraicGeometry.injective_frobeniusColimitSectionsComparison` and
  `AlgebraicGeometry.bijective_frobeniusColimitSectionsComparison`: **the comparison is bijective
  for a quasi-compact quasi-separated scheme.**

## Implementation notes

The two halves of bijectivity are
`AlgebraicGeometry.exists_frobeniusStructureSheafι_app_eq` and
`AlgebraicGeometry.exists_pow_eq_of_frobeniusStructureSheafι_app_eq`, both proved over an
arbitrary quasi-compact open; only the top open is used here, so quasi-compactness of `X` is the
hypothesis, and quasi-separatedness enters only through the surjectivity half.

The target of the comparison depends on the proof `hX` that `X` is in characteristic `p`, so the
comparison is not a morphism of presheaves on the category of schemes and its naturality is
stated as an equation of functions rather than as a `CategoryTheory.NatTrans`. That is all its
consumers need: the cartesian square of
`AlgebraicGeometry.isPullback_frobeniusColimit_twoGeneratorModel` is transported along the
comparison at each of the four corners of a square, and each corner comes with its own proof of
being in characteristic `p`.

Two places need the type of a map to be pinned before its body is elaborated.
`AlgebraicGeometry.frobeniusColimitSectionsLeg` is a separate definition rather than a lambda
inside the cocone because the sections of the structure sheaf have two spellings — `Γ(X, ⊤)` and
the value of the Frobenius tower at a stage — which are definitionally equal but which
`CategoryTheory.NatTrans.ofSequence` will not unify from the body alone. For the same reason
`AlgebraicGeometry.frobeniusColimitSectionsRestrict` names the restriction map: the codomain of
`AlgebraicGeometry.frobeniusColimitStructureSheafHom` is the pushforward sheaf, whose sections
over the top open are definitionally but not syntactically those of `colim_F 𝒪_X`, and a `rw`
whose motive crosses that identification fails with *"the target expression is not type-correct
under the `implicit` transparency level"*.

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius TopologicalSpace

universe u

namespace CategoryTheory.Presheaf

/-- **One step of the Frobenius tower of a presheaf of commutative rings, on an element**: the
transition from stage `n` to stage `n + 1` raises a section to its `p`-th power. This is
`CategoryTheory.Presheaf.frobeniusTower_map_succ` evaluated at an object and applied to a
section. It is stated for an arbitrary presheaf of commutative rings, where the value of the
tower at a stage reduces to the sections themselves; at a concrete presheaf the two spellings of
the sections no longer unify. -/
theorem frobeniusTowerAt_map_succ_apply {C : Type*} [Category* C] (G : Cᵒᵖ ⥤ CommRingCat.{u})
    (p : ℕ) (X : Cᵒᵖ) (n : ℕ) (a : ToType (G.obj X)) :
    (frobeniusTowerAt G p X).map (homOfLE n.le_succ) a = a ^ p := by
  change ((frobeniusTower G p).map (homOfLE n.le_succ)).app X a = a ^ p
  rw [frobeniusTower_map_succ]
  exact frobeniusForget_app G p X a

end CategoryTheory.Presheaf

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- The top open of a scheme is quasi-compact when the scheme is. -/
lemma isCompact_coe_top [CompactSpace X] : IsCompact ((⊤ : X.Opens) : Set X) := by
  rw [TopologicalSpace.Opens.coe_top]
  exact isCompact_univ

/-- The stage-`n + 1` coprojection of `colim_F 𝒪_X` on global sections absorbs one Frobenius: on
the `p`-th power of a global function it agrees with the stage-`n` coprojection. -/
lemma frobeniusStructureSheafι_app_top_pow (n : ℕ) (a : Γ(X, ⊤)) :
    (frobeniusStructureSheafι X p hX (n + 1)).hom.app (op ⊤) (a ^ p) =
      (frobeniusStructureSheafι X p hX n).hom.app (op ⊤) a := by
  rw [show a ^ p = a ^ p ^ 1 by rw [pow_one]]
  exact frobeniusStructureSheafι_pow_app X p hX n 1 ⊤ a

/-- The stage-`n` leg of the cocone of the coprojections: the stage-`n` coprojection of
`colim_F 𝒪_X` on global sections, with the sections of `𝒪_X` spelled as the value of the
Frobenius tower of `Γ(-, 𝒪)` at the stage. -/
noncomputable def frobeniusColimitSectionsLeg (n : ℕ) :
    (CategoryTheory.Presheaf.frobeniusTowerAt Scheme.Γ.{u} p (op X)).obj n ⟶
      ToType ((frobeniusColimitRingSheaf X p hX).obj.obj (op ⊤)) :=
  ↾(fun (a : (CategoryTheory.Presheaf.frobeniusTowerAt Scheme.Γ.{u} p (op X)).obj n) =>
      (frobeniusStructureSheafι X p hX n).hom.app (op ⊤) a)

/-- The stage-`n` leg is the stage-`n` coprojection on global sections. -/
lemma frobeniusColimitSectionsLeg_apply (n : ℕ) (a : Γ(X, ⊤)) :
    frobeniusColimitSectionsLeg X p hX n a =
      (frobeniusStructureSheafι X p hX n).hom.app (op ⊤) a := rfl

/-- **The cocone on the Frobenius tower of `Γ(X, 𝒪)` given by the coprojections of
`colim_F 𝒪_X`.** Its stage-`n` leg is the stage-`n` coprojection on global sections; the
compatibility is that moving up one stage of the tower raises a function to its `p`-th power,
which the coprojections absorb. -/
noncomputable def frobeniusColimitSectionsCocone :
    Cocone (CategoryTheory.Presheaf.frobeniusTowerAt Scheme.Γ.{u} p (op X)) where
  pt := ToType ((frobeniusColimitRingSheaf X p hX).obj.obj (op ⊤))
  ι := NatTrans.ofSequence (frobeniusColimitSectionsLeg X p hX)
    (fun n => by
      ext a
      refine Eq.trans (congrArg (fun t => frobeniusColimitSectionsLeg X p hX (n + 1) t)
        (CategoryTheory.Presheaf.frobeniusTowerAt_map_succ_apply Scheme.Γ.{u} p (op X) n a)) ?_
      exact frobeniusStructureSheafι_app_top_pow X p hX n a)

/-- **The comparison `colim_F Γ(X, 𝒪) ⟶ Γ(colim_F 𝒪_X, X)`.** A class of global functions
represented at stage `n` of the Frobenius tower goes to the image of a representative under the
stage-`n` coprojection of `colim_F 𝒪_X`; that is well defined because moving a representative up
a stage raises it to its `p`-th power, which the coprojections absorb. -/
noncomputable def frobeniusColimitSectionsComparison :
    (frobeniusColimitGlobalSections.{u} p).obj (op X) →
      ToType ((frobeniusColimitRingSheaf X p hX).obj.obj (op ⊤)) :=
  fun x => colimit.desc _ (frobeniusColimitSectionsCocone X p hX)
    ((CategoryTheory.Presheaf.frobeniusColimitObjIso Scheme.Γ.{u} p (op X)).hom x)

/-- **The comparison takes the class of a global function at stage `n` to its image under the
stage-`n` coprojection.** Since every class is represented at some stage, this determines the
comparison. -/
lemma frobeniusColimitSectionsComparison_stage (n : ℕ) (a : Γ(X, ⊤)) :
    frobeniusColimitSectionsComparison X p hX
        (CategoryTheory.Presheaf.frobeniusColimitStage Scheme.Γ.{u} p n (op X) a) =
      (frobeniusStructureSheafι X p hX n).hom.app (op ⊤) a := by
  have hinv : (CategoryTheory.Presheaf.frobeniusColimitObjIso Scheme.Γ.{u} p (op X)).inv
        (colimit.ι (CategoryTheory.Presheaf.frobeniusTowerAt Scheme.Γ.{u} p (op X)) n a) =
      CategoryTheory.Presheaf.frobeniusColimitStage Scheme.Γ.{u} p n (op X) a :=
    ConcreteCategory.congr_hom
      (colimitObjIsoColimitCompEvaluation_ι_inv
        (CategoryTheory.Presheaf.frobeniusTower Scheme.Γ.{u} p) n (op X)) a
  have hhom : (CategoryTheory.Presheaf.frobeniusColimitObjIso Scheme.Γ.{u} p (op X)).hom
        (CategoryTheory.Presheaf.frobeniusColimitStage Scheme.Γ.{u} p n (op X) a) =
      colimit.ι (CategoryTheory.Presheaf.frobeniusTowerAt Scheme.Γ.{u} p (op X)) n a := by
    rw [← hinv]
    exact (CategoryTheory.Presheaf.frobeniusColimitObjIso Scheme.Γ.{u} p (op X)).inv_hom_id_apply _
  have hd : colimit.desc (CategoryTheory.Presheaf.frobeniusTowerAt Scheme.Γ.{u} p (op X))
        (frobeniusColimitSectionsCocone X p hX)
        (colimit.ι (CategoryTheory.Presheaf.frobeniusTowerAt Scheme.Γ.{u} p (op X)) n a) =
      frobeniusColimitSectionsLeg X p hX n a :=
    ConcreteCategory.congr_hom (colimit.ι_desc (frobeniusColimitSectionsCocone X p hX) n) a
  change colimit.desc _ (frobeniusColimitSectionsCocone X p hX)
      ((CategoryTheory.Presheaf.frobeniusColimitObjIso Scheme.Γ.{u} p (op X)).hom
        (CategoryTheory.Presheaf.frobeniusColimitStage Scheme.Γ.{u} p n (op X) a)) = _
  rw [hhom]
  exact hd

/-- Two classes `ι n a` and `ι m b` of a tower whose images under `f` agree are equal, provided the
stage maps `g N` are injective up to the twists `T k`. -/
private theorem eq_of_comp_eq_of_twist_injective {A B C : Type*} (T : ℕ → A → A)
    (ι : ℕ → A → B) (g : ℕ → A → C) (f : B → C) (hι : ∀ n m a, ι n a = ι (n + m) (T m a))
    (hf : ∀ n a, f (ι n a) = g n a) (hg : ∀ N a b, g N a = g N b → ∃ k, T k a = T k b)
    {n m : ℕ} {a b : A} (h : f (ι n a) = f (ι m b)) : ι n a = ι m b := by
  have hb : ι m b = ι (n + m) (T n b) := by
    rw [Nat.add_comm n m]
    exact hι m n b
  rw [hι n m a, hb] at h ⊢
  obtain ⟨k, hk⟩ := hg _ _ _ ((hf _ _).symm.trans (h.trans (hf _ _)))
  rw [hι (n + m) k (T m a), hι (n + m) k (T n b), hk]

/-- **The comparison is injective for a quasi-compact scheme.** Two classes of global functions
with the same image are represented at a common stage, where two representatives with the same
image in `colim_F 𝒪_X` agree after enough Frobenius twists
(`AlgebraicGeometry.exists_pow_eq_of_frobeniusStructureSheafι_app_eq`), and raising a
representative to a `p`-power is moving it up the tower. -/
theorem injective_frobeniusColimitSectionsComparison [CompactSpace X] :
    Function.Injective (frobeniusColimitSectionsComparison X p hX) := by
  intro x y hxy
  obtain ⟨n, a, rfl⟩ :=
    CategoryTheory.Presheaf.exists_frobeniusColimitStage_eq Scheme.Γ.{u} p (op X) x
  obtain ⟨m, b, rfl⟩ :=
    CategoryTheory.Presheaf.exists_frobeniusColimitStage_eq Scheme.Γ.{u} p (op X) y
  exact eq_of_comp_eq_of_twist_injective (fun m a => a ^ p ^ m)
    (fun n a => CategoryTheory.Presheaf.frobeniusColimitStage Scheme.Γ.{u} p n (op X) a)
    (fun n a => (frobeniusStructureSheafι X p hX n).hom.app (op ⊤) a)
    (frobeniusColimitSectionsComparison X p hX)
    (fun n m a => CategoryTheory.Presheaf.frobeniusColimitStage_add Scheme.Γ.{u} p n m (op X) a)
    (frobeniusColimitSectionsComparison_stage X p hX)
    (fun N _ _ h => exists_pow_eq_of_frobeniusStructureSheafι_app_eq X p hX ⊤
      (isCompact_coe_top X) N _ _ h) hxy

/-- **The comparison is surjective for a quasi-compact quasi-separated scheme**, because every
section of `colim_F 𝒪_X` over a quasi-compact open of a quasi-separated scheme comes from a
finite stage (`AlgebraicGeometry.exists_frobeniusStructureSheafι_app_eq`). -/
theorem surjective_frobeniusColimitSectionsComparison [CompactSpace X]
    [QuasiSeparatedSpace X] :
    Function.Surjective (frobeniusColimitSectionsComparison X p hX) := by
  intro s
  obtain ⟨n, a, ha⟩ := exists_frobeniusStructureSheafι_app_eq X p hX ⊤
    (isCompact_coe_top X) s
  exact ⟨CategoryTheory.Presheaf.frobeniusColimitStage Scheme.Γ.{u} p n (op X) a,
    (frobeniusColimitSectionsComparison_stage X p hX n a).trans ha⟩

/-- **The comparison `colim_F Γ(X, 𝒪) ⟶ Γ(colim_F 𝒪_X, X)` is bijective for a quasi-compact
quasi-separated scheme.** This is what lets a cartesian square of Frobenius colimits of global
functions be read as a cartesian square of global sections of the Frobenius colimits of the
structure sheaves, which is the form the Hom-sets of
`AlgebraicGeometry.frobeniusColimitVectorBundles` are built from. -/
theorem bijective_frobeniusColimitSectionsComparison [CompactSpace X]
    [QuasiSeparatedSpace X] :
    Function.Bijective (frobeniusColimitSectionsComparison X p hX) :=
  ⟨injective_frobeniusColimitSectionsComparison X p hX,
    surjective_frobeniusColimitSectionsComparison X p hX⟩

/-! ### Sections over a quasi-compact open -/

/-- **The sheafification comparison is injective on sections over a quasi-compact open.** Two
elements of `colim_j 𝒪_X(U)` with the same image in `(colim_F 𝒪_X)(U)` are represented at a
common stage, where two representatives with the same image agree after enough Frobenius twists
(`AlgebraicGeometry.exists_pow_eq_of_frobeniusStructureSheafι_app_eq`); raising a representative
to a `p`-power is moving it up the tower, which does not change its class. -/
theorem injective_toFrobeniusColimitRingSheaf_app (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    Function.Injective ((toFrobeniusColimitRingSheaf X p hX).app (op U)) := by
  intro t t' h
  obtain ⟨n, a, rfl⟩ := exists_frobeniusRingPresheafι_app_eq X p hX U t
  obtain ⟨m, b, rfl⟩ := exists_frobeniusRingPresheafι_app_eq X p hX U t'
  exact eq_of_comp_eq_of_twist_injective (fun m a => a ^ p ^ m)
    (fun n a => (frobeniusRingPresheafι X p hX n).app (op U) a)
    (fun n a => (frobeniusStructureSheafι X p hX n).hom.app (op U) a)
    ((toFrobeniusColimitRingSheaf X p hX).app (op U))
    (fun n m a => (frobeniusRingPresheafι_pow_app X p hX n m U a).symm)
    (fun n a => (frobeniusStructureSheafι_hom_app X p hX n U a).symm)
    (fun N _ _ h => exists_pow_eq_of_frobeniusStructureSheafι_app_eq X p hX U hU N _ _ h) h

/-- **The sheafification comparison is surjective on sections over a quasi-compact open of a
quasi-separated scheme**, because every section of `colim_F 𝒪_X` there comes from a finite stage
(`AlgebraicGeometry.exists_frobeniusStructureSheafι_app_eq`), and the stage-`n` coprojection
factors through the presheaf colimit. -/
theorem surjective_toFrobeniusColimitRingSheaf_app [QuasiSeparatedSpace X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    Function.Surjective ((toFrobeniusColimitRingSheaf X p hX).app (op U)) := by
  intro s
  obtain ⟨n, a, ha⟩ := exists_frobeniusStructureSheafι_app_eq X p hX U hU s
  exact ⟨(frobeniusRingPresheafι X p hX n).app (op U) a,
    (frobeniusStructureSheafι_hom_app X p hX n U a).symm.trans ha⟩

/-- **No sheafification is needed over a quasi-compact open**: `(colim_F 𝒪_X)(U) = colim_j 𝒪_X(U)`
for `U` a quasi-compact open of a quasi-separated scheme. This is the comparison
`colim_F Γ(X, U) ⟶ Γ(colim_F 𝒪_X, U)` of Stacks Tag 0EXD over an arbitrary quasi-compact open,
packaged as a bijection; the comparison itself is
`AlgebraicGeometry.toFrobeniusColimitRingSheaf`, the sheafification map of the presheaf colimit,
and over the top open it is
`AlgebraicGeometry.bijective_frobeniusColimitSectionsComparison`. -/
theorem bijective_toFrobeniusColimitRingSheaf_app [QuasiSeparatedSpace X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    Function.Bijective ((toFrobeniusColimitRingSheaf X p hX).app (op U)) :=
  ⟨injective_toFrobeniusColimitRingSheaf_app X p hX U hU,
    surjective_toFrobeniusColimitRingSheaf_app X p hX U hU⟩

/-! ### Naturality -/

variable {X}

/-- **Restriction of global sections of `colim_F 𝒪` along a morphism of schemes** in
characteristic `p`: the canonical morphism `colim_F 𝒪_Y ⟶ f_*(colim_F 𝒪_X)` of
`AlgebraicGeometry.frobeniusColimitStructureSheafHom`, read on global sections. -/
noncomputable def frobeniusColimitSectionsRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) :
    ToType ((frobeniusColimitRingSheaf Y p hY).obj.obj (op ⊤)) →
      ToType ((frobeniusColimitRingSheaf X p hX).obj.obj (op ⊤)) :=
  fun y => (frobeniusColimitStructureSheafHom p f hX hY).hom.app (op ⊤) y

/-- **Restriction commutes with the coprojections.** The image of a global function of `Y` under
the stage-`n` coprojection of `colim_F 𝒪_Y` restricts to the image of its restriction under the
stage-`n` coprojection of `colim_F 𝒪_X`. This is
`AlgebraicGeometry.frobeniusColimitι_comp_frobeniusColimitStructureSheafHom` on global
sections. -/
lemma frobeniusColimitSectionsRestrict_stage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (n : ℕ) (b : Γ(Y, ⊤)) :
    frobeniusColimitSectionsRestrict p f hX hY
        ((frobeniusStructureSheafι Y p hY n).hom.app (op ⊤) b) =
      (frobeniusStructureSheafι X p hX n).hom.app (op ⊤) (f.appTop b) :=
  ConcreteCategory.congr_hom
    (congrArg (fun q : Y.ringSheafOnOpens ⟶
        (f.ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX) =>
      NatTrans.app q.hom (op (⊤ : Y.Opens)))
      (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p f hX hY n)) b

/-- **The comparison is natural in the scheme.** For a morphism `f : X ⟶ Y` of schemes in
characteristic `p`, restricting a class of global functions on `Y` along `f` and then comparing
is comparing on `Y` and then restricting the resulting global section of `colim_F 𝒪_Y`. -/
lemma frobeniusColimitSectionsComparison_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (x : (frobeniusColimitGlobalSections.{u} p).obj (op Y)) :
    frobeniusColimitSectionsComparison X p hX
        ((frobeniusColimitGlobalSections.{u} p).map f.op x) =
      frobeniusColimitSectionsRestrict p f hX hY
        (frobeniusColimitSectionsComparison Y p hY x) := by
  obtain ⟨n, b, rfl⟩ :=
    CategoryTheory.Presheaf.exists_frobeniusColimitStage_eq Scheme.Γ.{u} p (op Y) x
  refine Eq.trans (congrArg (frobeniusColimitSectionsComparison X p hX)
    (CategoryTheory.Presheaf.frobeniusColimit_map_stage Scheme.Γ.{u} p f.op n b)) ?_
  refine Eq.trans (frobeniusColimitSectionsComparison_stage X p hX n
    ((Scheme.Γ.map f.op).hom b)) ?_
  refine Eq.trans ?_ (congrArg (frobeniusColimitSectionsRestrict p f hX hY)
    (frobeniusColimitSectionsComparison_stage Y p hY n b)).symm
  exact (frobeniusColimitSectionsRestrict_stage p f hX hY n b).symm

end AlgebraicGeometry

end
